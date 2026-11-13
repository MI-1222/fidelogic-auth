//! # マルチスロット型エンベロープ暗号化状態機械 (FSM) モジュール。
//!
//! 形式検証モデル (`proofs/Theories/EnvelopeFsm.v`) で証明された、
//! 4状態 (`Locked`, `Unlocking`, `Unlocked`, `Zeroized`) と安全述語 `SafeState` を具現化する、
//! DEK (Data Encryption Key) ライフサイクル状態機械 [`VaultEngine`] を提供する。
//!
//! ## 形式検証モデルとの対応関係
//! - [`VaultState`] ⇄ `EnvelopeFsm.VaultState`
//! - [`SlotKind`] / [`SlotStatus`] / [`KekSlots`] ⇄ `EnvelopeFsm.SlotKind` / `SlotStatus` / `KekSlots`
//! - [`VaultEvent`] ⇄ `EnvelopeFsm.VaultEvent`
//! - [`VaultEngine`] ⇄ `EnvelopeFsm.VaultMachineState` + `step` / `machine_step`
//! - [`VaultEngine::is_safe_state`] ⇄ `EnvelopeFsm.SafeState` / `safe_stateb`
//! - [`VaultEngine::observe_dek`] ⇄ `EnvelopeFsm.observe_dek`

use core::mem::ManuallyDrop;

use crate::cipher::KEY_LEN;
use crate::error::VaultError;
use crate::kdf::Argon2Params;
use crate::zeroize::{SecretBytes, volatile_zeroize};

/// DEK (データ暗号化鍵) のバイト長 (256ビット = 32バイト)。
pub const DEK_LEN: usize = KEY_LEN;

/// スロット0 (Argon2id: マスターパスワード) のスロット識別子。
pub const SLOT_ID_ARGON2ID: u8 = 0;

/// スロット1 (WebAuthn PRF) のスロット識別子。
pub const SLOT_ID_PRF: u8 = 1;

/// スロット2 (リカバリーコード) のスロット識別子。
pub const SLOT_ID_RECOVERY: u8 = 2;

/// DEKのライフサイクル状態を表す列挙型。
///
/// `EnvelopeFsm.v` の帰納型 `VaultState` に対応し、
/// 未認証状態でのDEK保持やゼロ消去後の不正復帰を構造的に排除する。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VaultState {
    /// 施錠状態。メモリ上に平文DEKは存在しない。
    Locked,
    /// 解錠処理中の過渡状態。認証と鍵導出を実行中であり、平文DEKはまだ存在しない。
    Unlocking,
    /// 解錠状態。有効なKEKスロット経由で復号された平文DEKを保持する。
    Unlocked,
    /// ゼロ消去隔離状態。平文DEKはメモリ上で即時消去され、`reset` なしに解錠へ遷移できない。
    Zeroized,
}

impl VaultState {
    /// 現在の状態が [`VaultState::Locked`] であるかを判定する。
    #[inline]
    #[must_use]
    pub const fn is_locked(self) -> bool {
        matches!(self, Self::Locked)
    }

    /// 現在の状態が [`VaultState::Unlocking`] であるかを判定する。
    #[inline]
    #[must_use]
    pub const fn is_unlocking(self) -> bool {
        matches!(self, Self::Unlocking)
    }

    /// 現在の状態が [`VaultState::Unlocked`] であるかを判定する。
    #[inline]
    #[must_use]
    pub const fn is_unlocked(self) -> bool {
        matches!(self, Self::Unlocked)
    }

    /// 現在の状態が [`VaultState::Zeroized`] であるかを判定する。
    #[inline]
    #[must_use]
    pub const fn is_zeroized(self) -> bool {
        matches!(self, Self::Zeroized)
    }
}

/// 3つのKEKスロットの種別を表す列挙型。
///
/// `EnvelopeFsm.v` の `SlotKind` に対応する。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum SlotKind {
    /// スロット0 (Argon2id: マスターパスワード) スロット。
    Argon2id = SLOT_ID_ARGON2ID,
    /// スロット1 (WebAuthn PRF) スロット。
    Prf = SLOT_ID_PRF,
    /// スロット2 (リカバリーコード) スロット。
    Recovery = SLOT_ID_RECOVERY,
}

impl SlotKind {
    /// 数値スロットID (`0`, `1`, `2`) から [`SlotKind`] への変換を試みる。
    ///
    /// # Errors
    ///
    /// `id` が `0..=2` の範囲外である場合は [`VaultError::SlotNotFound`] を返す。
    #[inline]
    pub const fn from_slot_id(id: u8) -> Result<Self, VaultError> {
        match id {
            SLOT_ID_ARGON2ID => Ok(Self::Argon2id),
            SLOT_ID_PRF => Ok(Self::Prf),
            SLOT_ID_RECOVERY => Ok(Self::Recovery),
            _ => Err(VaultError::SlotNotFound),
        }
    }

    /// 本スロット種別に対応する数値スロットIDを返す。
    #[inline]
    #[must_use]
    pub const fn as_slot_id(self) -> u8 {
        self as u8
    }

    /// 指定された数値スロットIDが有効範囲 (`0`, `1`, `2`) であるかを判定する。
    ///
    /// `EnvelopeFsm.v` の `is_valid_slot_id` に対応する。
    #[inline]
    #[must_use]
    pub const fn is_valid_slot_id(id: u8) -> bool {
        matches!(id, SLOT_ID_ARGON2ID | SLOT_ID_PRF | SLOT_ID_RECOVERY)
    }
}

impl TryFrom<u8> for SlotKind {
    type Error = VaultError;

    #[inline]
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::from_slot_id(value)
    }
}

impl From<SlotKind> for u8 {
    #[inline]
    fn from(kind: SlotKind) -> Self {
        kind.as_slot_id()
    }
}

/// 単一KEKスロットの健全性状態を表す列挙型。
///
/// `EnvelopeFsm.v` の `SlotStatus` に対応する。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SlotStatus {
    /// ラップ済みDEKが復号可能で健全な状態。
    Valid,
    /// データ破損やフォーマット不正により復号不能な状態。
    Invalid,
    /// 未設定または未登録の状態。
    #[default]
    Unset,
}

impl SlotStatus {
    /// スロットが健全 ([`SlotStatus::Valid`]) であるかを判定する。
    ///
    /// `EnvelopeFsm.v` の `is_slot_status_valid` に対応する。
    #[inline]
    #[must_use]
    pub const fn is_valid(self) -> bool {
        matches!(self, Self::Valid)
    }
}

/// 3つのKEKスロット全体の健全性構成を保持する構造体。
///
/// `EnvelopeFsm.v` のレコード型 `KekSlots` に対応し、
/// スロット0 (Argon2id), スロット1 (WebAuthn PRF), スロット2 (リカバリーコード) の健全性を管理する。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct KekSlots {
    /// スロット0 (Argon2id: マスターパスワード) の健全性状態。
    pub argon2id: SlotStatus,
    /// スロット1 (WebAuthn PRF) の健全性状態。
    pub prf: SlotStatus,
    /// スロット2 (リカバリーコード) の健全性状態。
    pub recovery: SlotStatus,
}

impl KekSlots {
    /// 指定された各スロット状態から新しい [`KekSlots`] を構築する。
    #[inline]
    #[must_use]
    pub const fn new(argon2id: SlotStatus, prf: SlotStatus, recovery: SlotStatus) -> Self {
        Self {
            argon2id,
            prf,
            recovery,
        }
    }

    /// すべてのスロットが未設定 ([`SlotStatus::Unset`]) の構成を返す。
    #[inline]
    #[must_use]
    pub const fn unset_all() -> Self {
        Self {
            argon2id: SlotStatus::Unset,
            prf: SlotStatus::Unset,
            recovery: SlotStatus::Unset,
        }
    }

    /// スロットIDに対応する [`SlotStatus`] を取得する。
    ///
    /// `EnvelopeFsm.v` の `get_slot_status` に対応し、
    /// 境界外ID (`3` 以上) に対しては [`SlotStatus::Invalid`] を返す。
    #[inline]
    #[must_use]
    pub const fn status(self, slot_id: u8) -> SlotStatus {
        match slot_id {
            SLOT_ID_ARGON2ID => self.argon2id,
            SLOT_ID_PRF => self.prf,
            SLOT_ID_RECOVERY => self.recovery,
            _ => SlotStatus::Invalid,
        }
    }

    /// [`SlotKind`] に対応する [`SlotStatus`] を取得する。
    #[inline]
    #[must_use]
    pub const fn status_of(self, kind: SlotKind) -> SlotStatus {
        match kind {
            SlotKind::Argon2id => self.argon2id,
            SlotKind::Prf => self.prf,
            SlotKind::Recovery => self.recovery,
        }
    }

    /// 指定されたスロットIDのKEKスロットが健全であるかを判定する。
    ///
    /// `EnvelopeFsm.v` の `slot_validb` に対応する。
    #[inline]
    #[must_use]
    pub const fn is_slot_valid(self, slot_id: u8) -> bool {
        self.status(slot_id).is_valid()
    }

    /// 指定された [`SlotKind`] のKEKスロットが健全であるかを判定する。
    #[inline]
    #[must_use]
    pub const fn is_kind_valid(self, kind: SlotKind) -> bool {
        self.status_of(kind).is_valid()
    }

    /// 3つのKEKスロットのうち少なくとも1つが健全であるかを判定する。
    ///
    /// `EnvelopeFsm.v` の `any_slot_validb` (スロット多重化健全性) に対応する。
    #[inline]
    #[must_use]
    pub const fn any_valid(self) -> bool {
        self.argon2id.is_valid() || self.prf.is_valid() || self.recovery.is_valid()
    }

    /// 指定された [`SlotKind`] の健全性状態を更新する。
    #[inline]
    pub fn set_status(&mut self, kind: SlotKind, status: SlotStatus) {
        match kind {
            SlotKind::Argon2id => self.argon2id = status,
            SlotKind::Prf => self.prf = status,
            SlotKind::Recovery => self.recovery = status,
        }
    }
}

/// 状態遷移を駆動する入力イベントを表す列挙型。
///
/// `EnvelopeFsm.v` の `VaultEvent` に対応する。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VaultEvent {
    /// 指定スロット種別での解錠処理開始 (`Locked -> Unlocking`)。
    StartUnlock(SlotKind),
    /// 指定スロット種別での認証と復号成功 (`Unlocking -> Unlocked`)。
    UnlockSuccess(SlotKind),
    /// 認証または復号失敗 (`Unlocking -> Locked`)。
    UnlockFail,
    /// Vaultの施錠と平文DEK破棄 (`Unlocked -> Locked`)。
    Lock,
    /// 明示的なゼロ消去隔離 (`Unlocked -> Zeroized`)。
    Zeroize,
    /// ゼロ消去隔離状態からの再初期化 (`Zeroized -> Locked`)。
    Reset,
}

/// `EnvelopeFsm.v` の `VaultMachineState` と遷移関係を具現化する状態機械構造体。
///
/// ## 不変条件 (`SafeState`)
/// - `state` が [`VaultState::Locked`], [`VaultState::Unlocking`], [`VaultState::Zeroized`] の間、
///   内部の平文DEKバッファ (`dek`) は未初期化とみなされ、物理メモリ上はすべてゼロ消去状態に保たれる。
/// - `state` が [`VaultState::Unlocked`] の間のみ、有効な [`SecretBytes<DEK_LEN>`] を保持する。
/// - [`ManuallyDrop`] による透明なバッファ管理を採用し、`Option` の判別タグ領域に対する
///   `unsafe` な生ゼロ書き込みを排除することで未定義動作 (UB) を回避しつつ、
///   ゼロコストで安全なインプレース消去を実現する。
/// - 施錠, ゼロ消去, 失敗時の破棄, インスタンス破棄 (`Drop`) の各処理では、
///   `volatile_zeroize` によるインプレース揮発性ゼロ書き込みとコンパイラフェンスを実行し、
///   Dead Store Elimination (DSE) による消去命令の除去を防止する。
pub struct VaultEngine {
    state: VaultState,
    dek: ManuallyDrop<SecretBytes<DEK_LEN>>,
    slots: KekSlots,
    dummy_argon2_params: Argon2Params,
}

impl VaultEngine {
    /// 指定されたKEKスロット構成で、施錠状態の新しい [`VaultEngine`] を生成する。
    ///
    /// 初期状態は [`VaultState::Locked`] かつ平文DEKはゼロクリアされており、
    /// `SafeState` 不変条件を常に満たす。
    #[inline]
    #[must_use]
    pub const fn new(slots: KekSlots) -> Self {
        Self {
            state: VaultState::Locked,
            dek: ManuallyDrop::new(SecretBytes::zero()),
            slots,
            dummy_argon2_params: Argon2Params::default_for_target(),
        }
    }

    /// 全スロット未設定かつ施錠状態の新しい [`VaultEngine`] を生成する。
    #[inline]
    #[must_use]
    pub const fn locked() -> Self {
        Self::new(KekSlots::unset_all())
    }

    /// スロット0不在または破損時のダミー暗号演算に用いる [`Argon2Params`] を上書きする。
    #[inline]
    #[must_use]
    pub const fn with_dummy_argon2_params(mut self, params: Argon2Params) -> Self {
        self.dummy_argon2_params = params;
        self
    }

    /// スロット0不在または破損時のダミー暗号演算に用いる [`Argon2Params`] を取得する。
    #[inline]
    #[must_use]
    pub const fn dummy_argon2_params(&self) -> &Argon2Params {
        &self.dummy_argon2_params
    }

    /// スロット0不在または破損時のダミー暗号演算に用いる [`Argon2Params`] を更新する。
    #[inline]
    pub fn set_dummy_argon2_params(&mut self, params: Argon2Params) {
        self.dummy_argon2_params = params;
    }

    /// 現在のライフサイクル状態 ([`VaultState`]) を返す。
    #[inline]
    #[must_use]
    pub const fn state(&self) -> VaultState {
        self.state
    }

    /// 現在のKEKスロット構成 ([`KekSlots`]) への参照を返す。
    #[inline]
    #[must_use]
    pub const fn slots(&self) -> &KekSlots {
        &self.slots
    }

    /// KEKスロット構成全体を更新する。
    ///
    /// # Errors
    ///
    /// 現在の状態が [`VaultState::Unlocking`] である場合は、
    /// 解錠遷移中の不変条件保護のため [`VaultError::InvalidState`] を返す。
    #[inline]
    pub fn set_slots(&mut self, slots: KekSlots) -> Result<(), VaultError> {
        if self.state == VaultState::Unlocking {
            return Err(VaultError::InvalidState);
        }
        self.slots = slots;
        Ok(())
    }

    /// 指定されたスロット種別の健全性状態を更新する。
    ///
    /// # Errors
    ///
    /// 現在の状態が [`VaultState::Unlocking`] である場合は、
    /// 解錠遷移中の不変条件保護のため [`VaultError::InvalidState`] を返す。
    #[inline]
    pub fn set_slot_status(
        &mut self,
        kind: SlotKind,
        status: SlotStatus,
    ) -> Result<(), VaultError> {
        if self.state == VaultState::Unlocking {
            return Err(VaultError::InvalidState);
        }
        self.slots.set_status(kind, status);
        Ok(())
    }

    /// 現在のマシン状態が安全述語 `SafeState` を満たしているかを検証する。
    ///
    /// `EnvelopeFsm.v` の `safe_stateb` に対応し、
    /// `self.state == VaultState::Unlocked` のときのみ初期化済みとみなし、
    /// 非解錠状態 (`Locked`, `Unlocking`, `Zeroized`) では平文DEKバッファが
    /// 物理メモリ上で完全にゼロ消去されていることを確認する。
    #[inline]
    #[must_use]
    pub fn is_safe_state(&self) -> bool {
        match self.state {
            VaultState::Locked | VaultState::Unlocking | VaultState::Zeroized => {
                self.dek.as_bytes().iter().all(|&b| b == 0)
            }
            VaultState::Unlocked => true,
        }
    }

    /// 現在のマシン状態から平文DEKを安全に観測する。
    ///
    /// `EnvelopeFsm.v` の `observe_dek` に対応し、
    /// 状態が [`VaultState::Unlocked`] の場合のみ平文DEKへの参照を返す。
    /// 非解錠状態では常に `None` を返す。
    #[inline]
    #[must_use]
    pub fn observe_dek(&self) -> Option<&SecretBytes<DEK_LEN>> {
        match self.state {
            VaultState::Unlocked => Some(&self.dek),
            VaultState::Locked | VaultState::Unlocking | VaultState::Zeroized => None,
        }
    }

    /// 解錠状態の平文DEKへの参照を取得する。
    ///
    /// # Errors
    ///
    /// 状態が [`VaultState::Unlocked`] でない場合、またはDEKが保持されていない場合は
    /// [`VaultError::InvalidState`] を返す。
    #[inline]
    pub fn dek(&self) -> Result<&SecretBytes<DEK_LEN>, VaultError> {
        self.observe_dek().ok_or(VaultError::InvalidState)
    }

    /// 解錠状態の平文DEKを用いたクロージャを実行し、所有権を外部へ逃がさず結果を返す。
    ///
    /// # Errors
    ///
    /// 状態が [`VaultState::Unlocked`] でない場合は [`VaultError::InvalidState`] を返す。
    #[inline]
    pub fn with_dek<F, R>(&self, f: F) -> Result<R, VaultError>
    where
        F: FnOnce(&SecretBytes<DEK_LEN>) -> R,
    {
        let dek = self.dek()?;
        Ok(f(dek))
    }

    /// 指定された [`VaultEvent`] が現在の状態とスロット構成のもとで合法な遷移であるかを判定する。
    ///
    /// `EnvelopeFsm.v` の遷移関係 `step` の単一ステップ前提条件に対応する。
    #[inline]
    #[must_use]
    pub const fn can_step(&self, event: VaultEvent) -> bool {
        match (self.state, event) {
            (VaultState::Locked, VaultEvent::StartUnlock(_)) => true,
            (VaultState::Unlocking, VaultEvent::UnlockSuccess(kind)) => {
                self.slots.is_kind_valid(kind)
            }
            (VaultState::Unlocking, VaultEvent::UnlockFail)
            | (VaultState::Unlocked, VaultEvent::Lock | VaultEvent::Zeroize)
            | (VaultState::Zeroized, VaultEvent::Reset) => true,
            _ => false,
        }
    }

    /// 内部の平文DEKバッファをインプレースで揮発性ゼロクリアする。
    ///
    /// [`ManuallyDrop`] により `Option` の判別タグ領域やスタックコピーが存在せず、
    /// `unsafe` なタグ破壊ゼロ書き込みを排除して、既存のバッファ領域そのものに対して
    /// 安全に `volatile_zeroize` を適用する。
    #[inline]
    fn scrub_dek_in_place(&mut self) {
        volatile_zeroize(self.dek.as_mut_slice());
    }

    /// 解錠処理を開始し、`Locked` から `Unlocking` へ遷移する (`StepStartUnlock`)。
    ///
    /// # Errors
    ///
    /// 現在の状態が [`VaultState::Locked`] でない場合は [`VaultError::InvalidState`] を返す。
    pub fn start_unlock(&mut self, _kind: SlotKind) -> Result<(), VaultError> {
        if self.state != VaultState::Locked {
            return Err(VaultError::InvalidState);
        }
        self.scrub_dek_in_place();
        self.state = VaultState::Unlocking;
        Ok(())
    }

    /// 認証と復号の成功に伴い平文DEKをロードし、`Unlocking` から `Unlocked` へ遷移する (`StepUnlockSuccess`)。
    ///
    /// 状態不正やスロット無効等により遷移が拒絶された場合でも、
    /// 引数で受け取った `dek` は返却前に `volatile_zeroize` により即時消去される。
    ///
    /// # Errors
    ///
    /// - 現在の状態が [`VaultState::Unlocking`] でない場合は [`VaultError::InvalidState`] を返す。
    /// - 対象スロットが健全 ([`SlotStatus::Valid`]) でない場合は [`VaultError::AuthenticationFailed`] を返す。
    pub fn complete_unlock(
        &mut self,
        kind: SlotKind,
        mut dek: SecretBytes<DEK_LEN>,
    ) -> Result<(), VaultError> {
        if self.state != VaultState::Unlocking {
            volatile_zeroize(dek.as_mut_slice());
            return Err(VaultError::InvalidState);
        }
        if !self.slots.is_kind_valid(kind) {
            volatile_zeroize(dek.as_mut_slice());
            return Err(VaultError::AuthenticationFailed);
        }

        self.scrub_dek_in_place();
        self.dek = ManuallyDrop::new(dek);
        self.state = VaultState::Unlocked;
        Ok(())
    }

    /// 認証または復号の失敗を通知し、`Unlocking` から `Locked` へ復帰する (`StepUnlockFail`)。
    ///
    /// # Errors
    ///
    /// 現在の状態が [`VaultState::Unlocking`] でない場合は [`VaultError::InvalidState`] を返す。
    pub fn fail_unlock(&mut self) -> Result<(), VaultError> {
        if self.state != VaultState::Unlocking {
            return Err(VaultError::InvalidState);
        }
        self.scrub_dek_in_place();
        self.state = VaultState::Locked;
        Ok(())
    }

    /// Vaultを施錠し、保持している平文DEKを即時ゼロ消去して `Locked` へ遷移する (`StepLock`)。
    ///
    /// # Errors
    ///
    /// 現在の状態が [`VaultState::Unlocked`] でない場合は [`VaultError::InvalidState`] を返す。
    pub fn lock(&mut self) -> Result<(), VaultError> {
        if self.state != VaultState::Unlocked {
            return Err(VaultError::InvalidState);
        }
        self.scrub_dek_in_place();
        self.state = VaultState::Locked;
        Ok(())
    }

    /// 平文DEKを即時ゼロ消去し、`Unlocked` から `Zeroized` 隔離状態へ遷移する (`StepZeroize`)。
    ///
    /// `EnvelopeFsm.v` の `StepZeroize` に厳密に準拠し、[`VaultState::Unlocked`] からのみ遷移を許可する。
    /// 任意の現在状態から無条件に破棄・隔離を行う場合は [`VaultEngine::emergency_zeroize`] を使用する。
    ///
    /// # Errors
    ///
    /// 現在の状態が [`VaultState::Unlocked`] でない場合は [`VaultError::InvalidState`] を返す。
    pub fn zeroize_key(&mut self) -> Result<(), VaultError> {
        if self.state != VaultState::Unlocked {
            return Err(VaultError::InvalidState);
        }
        self.scrub_dek_in_place();
        self.state = VaultState::Zeroized;
        Ok(())
    }

    /// 現在の状態に関わらず、保持中の平文DEKを無条件に即時ゼロ消去して [`VaultState::Zeroized`] へ隔離する。
    ///
    /// エラーから復帰できない場合の緊急鍵破棄や、ゼロ化隔離として使用する。
    #[inline]
    pub fn emergency_zeroize(&mut self) {
        self.scrub_dek_in_place();
        self.state = VaultState::Zeroized;
    }

    /// ゼロ消去隔離状態から再初期化を実行し、`Zeroized` から `Locked` へ復帰する (`StepReset`)。
    ///
    /// `EnvelopeFsm.v` の `steps_zeroized_to_unlocked_requires_reset` が保証するとおり、
    /// `Zeroized` 状態から再度解錠するには必ず本メソッドによる再初期化を経由する必要がある。
    ///
    /// # Errors
    ///
    /// 現在の状態が [`VaultState::Zeroized`] でない場合は [`VaultError::InvalidState`] を返す。
    pub fn reset(&mut self) -> Result<(), VaultError> {
        if self.state != VaultState::Zeroized {
            return Err(VaultError::InvalidState);
        }
        self.scrub_dek_in_place();
        self.state = VaultState::Locked;
        Ok(())
    }
}

impl Default for VaultEngine {
    #[inline]
    fn default() -> Self {
        Self::locked()
    }
}

impl core::fmt::Debug for VaultEngine {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("VaultEngine")
            .field("state", &self.state)
            .field("has_dek", &(self.state == VaultState::Unlocked))
            .field("slots", &self.slots)
            .finish()
    }
}

impl zeroize::Zeroize for VaultEngine {
    #[inline]
    fn zeroize(&mut self) {
        self.emergency_zeroize();
    }
}

impl zeroize::ZeroizeOnDrop for VaultEngine {}

impl Drop for VaultEngine {
    #[inline]
    fn drop(&mut self) {
        self.scrub_dek_in_place();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use zeroize::Zeroize;

    fn sample_dek(seed: u8) -> SecretBytes<DEK_LEN> {
        SecretBytes::new([seed; DEK_LEN])
    }

    fn all_valid_slots() -> KekSlots {
        KekSlots::new(SlotStatus::Valid, SlotStatus::Valid, SlotStatus::Valid)
    }

    #[test]
    fn test_initial_state_satisfies_safe_state() {
        let engine = VaultEngine::new(all_valid_slots());
        assert_eq!(engine.state(), VaultState::Locked);
        assert!(engine.state().is_locked());
        assert!(engine.is_safe_state(), "初期状態でのSafeState確認に成功。");
        assert!(
            engine.observe_dek().is_none(),
            "Locked状態でのDEK非観測確認に成功。"
        );
        assert_eq!(engine.dek().err(), Some(VaultError::InvalidState));
        assert_eq!(
            engine.with_dek(|k| k[0]),
            Err(VaultError::InvalidState),
            "Locked状態でのwith_dek拒絶に成功。"
        );

        let default_engine = VaultEngine::default();
        assert_eq!(default_engine.state(), VaultState::Locked);
        assert!(default_engine.is_safe_state());
        assert!(!default_engine.slots().any_valid());
    }

    #[test]
    fn test_slot_kind_and_kek_slots_model_consistency() {
        assert_eq!(
            SlotKind::from_slot_id(SLOT_ID_ARGON2ID),
            Ok(SlotKind::Argon2id)
        );
        assert_eq!(SlotKind::from_slot_id(SLOT_ID_PRF), Ok(SlotKind::Prf));
        assert_eq!(
            SlotKind::from_slot_id(SLOT_ID_RECOVERY),
            Ok(SlotKind::Recovery)
        );
        assert_eq!(SlotKind::from_slot_id(3), Err(VaultError::SlotNotFound));
        assert_eq!(SlotKind::from_slot_id(255), Err(VaultError::SlotNotFound));

        assert!(SlotKind::is_valid_slot_id(0));
        assert!(SlotKind::is_valid_slot_id(1));
        assert!(SlotKind::is_valid_slot_id(2));
        assert!(!SlotKind::is_valid_slot_id(3));

        assert_eq!(SlotStatus::default(), SlotStatus::Unset);
        assert_eq!(KekSlots::default(), KekSlots::unset_all());

        let mut slots = KekSlots::new(SlotStatus::Invalid, SlotStatus::Unset, SlotStatus::Valid);
        assert_eq!(slots.status(0), SlotStatus::Invalid);
        assert_eq!(slots.status(1), SlotStatus::Unset);
        assert_eq!(slots.status(2), SlotStatus::Valid);
        assert_eq!(
            slots.status(99),
            SlotStatus::Invalid,
            "境界外スロットIDに対するSlotStatus::Invalid返却に成功。"
        );
        assert!(!slots.is_slot_valid(0));
        assert!(!slots.is_slot_valid(1));
        assert!(slots.is_slot_valid(2));
        assert!(!slots.is_slot_valid(99));
        assert!(slots.any_valid());

        slots.set_status(SlotKind::Recovery, SlotStatus::Invalid);
        assert!(!slots.any_valid());
        assert_eq!(slots.status_of(SlotKind::Recovery), SlotStatus::Invalid);
    }

    #[test]
    fn test_valid_unlock_lock_zeroize_reset_lifecycle() {
        let mut engine = VaultEngine::new(all_valid_slots());

        assert!(engine.can_step(VaultEvent::StartUnlock(SlotKind::Argon2id)));
        assert!(!engine.can_step(VaultEvent::UnlockSuccess(SlotKind::Argon2id)));
        assert_eq!(engine.start_unlock(SlotKind::Argon2id), Ok(()));
        assert_eq!(engine.state(), VaultState::Unlocking);
        assert!(engine.state().is_unlocking());
        assert!(engine.is_safe_state());
        assert!(engine.observe_dek().is_none());

        assert!(engine.can_step(VaultEvent::UnlockSuccess(SlotKind::Argon2id)));
        assert_eq!(
            engine.complete_unlock(SlotKind::Argon2id, sample_dek(0xA5)),
            Ok(())
        );
        assert_eq!(engine.state(), VaultState::Unlocked);
        assert!(engine.state().is_unlocked());
        assert!(engine.is_safe_state());
        assert_eq!(
            engine.observe_dek().map(SecretBytes::as_bytes),
            Some(&[0xA5u8; DEK_LEN]),
            "Unlocked状態でのDEK取得に成功。"
        );
        assert_eq!(engine.with_dek(|k| k[0]), Ok(0xA5));

        assert!(engine.can_step(VaultEvent::Lock));
        assert_eq!(engine.lock(), Ok(()));
        assert_eq!(engine.state(), VaultState::Locked);
        assert!(engine.is_safe_state());
        assert!(
            engine.observe_dek().is_none(),
            "施錠後のDEK消去確認に成功。"
        );

        assert_eq!(engine.start_unlock(SlotKind::Prf), Ok(()));
        assert_eq!(
            engine.complete_unlock(SlotKind::Prf, sample_dek(0x5A)),
            Ok(())
        );
        assert!(engine.can_step(VaultEvent::Zeroize));
        assert_eq!(engine.zeroize_key(), Ok(()));
        assert_eq!(engine.state(), VaultState::Zeroized);
        assert!(engine.state().is_zeroized());
        assert!(engine.is_safe_state());
        assert!(
            engine.observe_dek().is_none(),
            "ゼロ消去後のDEK消去確認に成功。"
        );

        assert!(
            !engine.can_step(VaultEvent::StartUnlock(SlotKind::Argon2id)),
            "Zeroized状態からのResetを経ないStartUnlock拒絶に成功。"
        );
        assert_eq!(
            engine.start_unlock(SlotKind::Argon2id),
            Err(VaultError::InvalidState)
        );
        assert!(engine.can_step(VaultEvent::Reset));
        assert_eq!(engine.reset(), Ok(()));
        assert_eq!(engine.state(), VaultState::Locked);
        assert!(engine.is_safe_state());
    }

    #[test]
    fn test_slot_multiplexing_unlock_with_single_valid_slot() {
        for valid_kind in [SlotKind::Argon2id, SlotKind::Prf, SlotKind::Recovery] {
            let mut slots =
                KekSlots::new(SlotStatus::Invalid, SlotStatus::Unset, SlotStatus::Invalid);
            slots.set_status(valid_kind, SlotStatus::Valid);
            assert!(slots.any_valid());

            let mut engine = VaultEngine::new(slots);
            assert_eq!(engine.start_unlock(valid_kind), Ok(()));
            assert_eq!(engine.complete_unlock(valid_kind, sample_dek(0x33)), Ok(()));
            assert_eq!(engine.state(), VaultState::Unlocked);
            assert!(engine.is_safe_state());
        }
    }

    #[test]
    fn test_illegal_transitions_are_rejected_and_preserve_safe_state() {
        let mut engine = VaultEngine::new(all_valid_slots());

        assert_eq!(
            engine.complete_unlock(SlotKind::Argon2id, sample_dek(0x11)),
            Err(VaultError::InvalidState),
            "LockedからUnlockedへの直接遷移拒絶に成功。"
        );
        assert_eq!(engine.state(), VaultState::Locked);
        assert!(engine.is_safe_state());

        assert_eq!(engine.fail_unlock(), Err(VaultError::InvalidState));
        assert_eq!(engine.lock(), Err(VaultError::InvalidState));
        assert_eq!(engine.zeroize_key(), Err(VaultError::InvalidState));
        assert_eq!(engine.reset(), Err(VaultError::InvalidState));

        assert_eq!(engine.start_unlock(SlotKind::Argon2id), Ok(()));
        assert_eq!(
            engine.start_unlock(SlotKind::Prf),
            Err(VaultError::InvalidState)
        );
        assert_eq!(engine.lock(), Err(VaultError::InvalidState));
        assert_eq!(engine.zeroize_key(), Err(VaultError::InvalidState));
        assert_eq!(engine.reset(), Err(VaultError::InvalidState));
        assert_eq!(engine.state(), VaultState::Unlocking);
        assert!(engine.is_safe_state());

        assert_eq!(engine.fail_unlock(), Ok(()));
        assert_eq!(engine.state(), VaultState::Locked);
        assert!(engine.is_safe_state());
    }

    #[test]
    fn test_invalid_or_unset_slot_cannot_complete_unlock() {
        let slots = KekSlots::new(SlotStatus::Invalid, SlotStatus::Unset, SlotStatus::Valid);
        let mut engine = VaultEngine::new(slots);

        assert_eq!(engine.start_unlock(SlotKind::Argon2id), Ok(()));
        assert_eq!(
            engine.complete_unlock(SlotKind::Argon2id, sample_dek(0x77)),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(engine.state(), VaultState::Unlocking);
        assert!(engine.is_safe_state());
        assert_eq!(engine.fail_unlock(), Ok(()));
        assert_eq!(engine.state(), VaultState::Locked);

        assert_eq!(engine.start_unlock(SlotKind::Prf), Ok(()));
        assert_eq!(
            engine.complete_unlock(SlotKind::Prf, sample_dek(0x88)),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(engine.fail_unlock(), Ok(()));
        assert_eq!(engine.state(), VaultState::Locked);
    }

    #[test]
    fn test_set_slots_and_slot_status_state_guards() {
        let mut engine = VaultEngine::new(all_valid_slots());

        // Locked状態: スロット更新および個別ステータス変更が可能。
        let new_slots = KekSlots::new(SlotStatus::Invalid, SlotStatus::Valid, SlotStatus::Unset);
        assert_eq!(engine.set_slots(new_slots), Ok(()));
        assert_eq!(*engine.slots(), new_slots);
        assert_eq!(
            engine.set_slot_status(SlotKind::Argon2id, SlotStatus::Valid),
            Ok(())
        );
        assert_eq!(
            engine.slots().status_of(SlotKind::Argon2id),
            SlotStatus::Valid
        );

        // Unlocking状態への遷移: 解錠処理中におけるスロット変更は不変条件保護のため拒絶される。
        assert_eq!(engine.start_unlock(SlotKind::Argon2id), Ok(()));
        assert_eq!(engine.state(), VaultState::Unlocking);

        let rejected_slots = KekSlots::unset_all();
        assert_eq!(
            engine.set_slots(rejected_slots),
            Err(VaultError::InvalidState),
            "Unlocking状態でのset_slots拒絶に成功。"
        );
        assert_eq!(
            engine.set_slot_status(SlotKind::Argon2id, SlotStatus::Invalid),
            Err(VaultError::InvalidState),
            "Unlocking状態でのset_slot_status拒絶に成功。"
        );
        // スロット構成が破壊されていないことを検証。
        assert_eq!(
            engine.slots().status_of(SlotKind::Argon2id),
            SlotStatus::Valid
        );

        // 復号完了してUnlockedへ遷移: スロット更新が可能。
        assert_eq!(
            engine.complete_unlock(SlotKind::Argon2id, sample_dek(0x42)),
            Ok(())
        );
        assert_eq!(engine.state(), VaultState::Unlocked);
        assert_eq!(
            engine.set_slot_status(SlotKind::Prf, SlotStatus::Invalid),
            Ok(()),
            "Unlocked状態でのset_slot_status更新に成功。"
        );
        assert_eq!(engine.slots().status_of(SlotKind::Prf), SlotStatus::Invalid);

        // Zeroized状態へ隔離後: スロット更新が可能。
        assert_eq!(engine.zeroize_key(), Ok(()));
        assert_eq!(engine.state(), VaultState::Zeroized);
        assert_eq!(
            engine.set_slots(all_valid_slots()),
            Ok(()),
            "Zeroized状態でのset_slots更新に成功。"
        );
        assert_eq!(*engine.slots(), all_valid_slots());
    }

    #[test]
    fn test_zeroized_quarantine_blocks_unlock_until_reset() {
        let mut engine = VaultEngine::new(all_valid_slots());
        engine.start_unlock(SlotKind::Recovery).unwrap();
        engine
            .complete_unlock(SlotKind::Recovery, sample_dek(0xCC))
            .unwrap();
        engine.zeroize_key().unwrap();

        assert_eq!(
            engine.start_unlock(SlotKind::Argon2id),
            Err(VaultError::InvalidState)
        );
        assert_eq!(
            engine.complete_unlock(SlotKind::Argon2id, sample_dek(0xDD)),
            Err(VaultError::InvalidState)
        );
        assert_eq!(engine.fail_unlock(), Err(VaultError::InvalidState));
        assert_eq!(engine.lock(), Err(VaultError::InvalidState));
        assert_eq!(engine.zeroize_key(), Err(VaultError::InvalidState));
        assert_eq!(engine.state(), VaultState::Zeroized);
        assert!(engine.observe_dek().is_none());
        assert!(engine.is_safe_state());
    }

    #[test]
    fn test_emergency_zeroize_and_zeroize_trait_and_debug_redaction() {
        extern crate alloc;
        use alloc::format;

        for initial_target in [
            VaultState::Locked,
            VaultState::Unlocking,
            VaultState::Unlocked,
        ] {
            let mut engine = VaultEngine::new(all_valid_slots());
            match initial_target {
                VaultState::Locked => {}
                VaultState::Unlocking => {
                    engine.start_unlock(SlotKind::Argon2id).unwrap();
                }
                VaultState::Unlocked => {
                    engine.start_unlock(SlotKind::Argon2id).unwrap();
                    engine
                        .complete_unlock(SlotKind::Argon2id, sample_dek(0xEE))
                        .unwrap();
                    let debug_str = format!("{engine:?}");
                    assert!(
                        !debug_str.contains("ee"),
                        "Debug出力における平文DEKバイト列の非漏洩確認に成功。"
                    );
                    assert!(debug_str.contains("has_dek: true"));
                }
                VaultState::Zeroized => {}
            }
            engine.emergency_zeroize();
            assert_eq!(engine.state(), VaultState::Zeroized);
            assert!(engine.observe_dek().is_none());
            assert!(engine.is_safe_state());
        }

        let mut engine_trait = VaultEngine::new(all_valid_slots());
        engine_trait.start_unlock(SlotKind::Prf).unwrap();
        engine_trait
            .complete_unlock(SlotKind::Prf, sample_dek(0xFE))
            .unwrap();
        Zeroize::zeroize(&mut engine_trait);
        assert_eq!(engine_trait.state(), VaultState::Zeroized);
        assert!(engine_trait.observe_dek().is_none());
        assert!(engine_trait.is_safe_state());
    }

    #[test]
    fn test_scrub_dek_in_place_clears_backing_memory() {
        let mut engine = VaultEngine::new(all_valid_slots());
        engine.start_unlock(SlotKind::Argon2id).unwrap();
        engine
            .complete_unlock(SlotKind::Argon2id, sample_dek(0x99))
            .unwrap();

        let dek_ptr = engine
            .observe_dek()
            .expect("Unlocked状態におけるDEK存在確認に成功。")
            .as_ptr();
        // SAFETY: `dek_ptr` は `engine` が生存中に取得した32バイト配列の先頭ポインタである。
        let observed_nonzero = unsafe {
            let slice = core::slice::from_raw_parts(dek_ptr, DEK_LEN);
            slice.iter().all(|&b| b == 0x99)
        };
        assert!(observed_nonzero);

        // `lock()` 実行時に `Option::Some(SecretBytes)` の内部配列が確実にゼロクリアされることを検証する。
        // Drop前のインプレース消去を直接確認するため、`scrub_dek_in_place` と同一経路を通る `lock()` を呼ぶ。
        engine.lock().unwrap();
        assert_eq!(engine.state(), VaultState::Locked);
        assert!(engine.observe_dek().is_none());
        assert!(engine.is_safe_state());

        // SAFETY: `engine` は生存しており、`dek_ptr` が指していたメモリ領域は
        // `scrub_dek_in_place()` により揮発性ゼロ書き込み (`volatile_zeroize`) されている。
        // コンパイラ最適化による読み飛ばしを抑止して物理メモリ上のゼロ消去を直接検証するため、各バイトを揮発性読み出しで確認する。
        let observed_zero = unsafe {
            (0..DEK_LEN).all(|offset| core::ptr::read_volatile(dek_ptr.add(offset)) == 0)
        };
        assert!(
            observed_zero,
            "lock() 実行後の DEK メモリ領域が確実にゼロクリアされていることを確認。"
        );
    }

    fn arb_slot_status() -> impl Strategy<Value = SlotStatus> {
        prop_oneof![
            Just(SlotStatus::Valid),
            Just(SlotStatus::Invalid),
            Just(SlotStatus::Unset),
        ]
    }

    fn arb_kek_slots() -> impl Strategy<Value = KekSlots> {
        (arb_slot_status(), arb_slot_status(), arb_slot_status())
            .prop_map(|(a, p, r)| KekSlots::new(a, p, r))
    }

    fn arb_slot_kind() -> impl Strategy<Value = SlotKind> {
        prop_oneof![
            Just(SlotKind::Argon2id),
            Just(SlotKind::Prf),
            Just(SlotKind::Recovery),
        ]
    }

    fn arb_vault_event() -> impl Strategy<Value = VaultEvent> {
        prop_oneof![
            arb_slot_kind().prop_map(VaultEvent::StartUnlock),
            arb_slot_kind().prop_map(VaultEvent::UnlockSuccess),
            Just(VaultEvent::UnlockFail),
            Just(VaultEvent::Lock),
            Just(VaultEvent::Zeroize),
            Just(VaultEvent::Reset),
        ]
    }

    proptest! {
        #[test]
        fn prop_arbitrary_event_trace_preserves_safe_state_and_non_auth_confidentiality(
            slots in arb_kek_slots(),
            events in prop::collection::vec(arb_vault_event(), 0..64),
            dek_seed in any::<u8>(),
        ) {
            let mut engine = VaultEngine::new(slots);
            let mut saw_valid_unlock = false;

            prop_assert!(engine.is_safe_state());
            prop_assert!(engine.observe_dek().is_none());

            for ev in events {
                let prev_state = engine.state();
                let can = engine.can_step(ev);

                let res = match ev {
                    VaultEvent::StartUnlock(id) => engine.start_unlock(id),
                    VaultEvent::UnlockSuccess(id) => {
                        let r = engine.complete_unlock(id, sample_dek(dek_seed));
                        if r.is_ok() {
                            saw_valid_unlock = true;
                        }
                        r
                    }
                    VaultEvent::UnlockFail => engine.fail_unlock(),
                    VaultEvent::Lock => engine.lock(),
                    VaultEvent::Zeroize => engine.zeroize_key(),
                    VaultEvent::Reset => engine.reset(),
                };

                prop_assert_eq!(res.is_ok(), can, "can_step判定と実際の遷移成否の一致確認に成功。");
                prop_assert!(engine.is_safe_state(), "任意イベント実行後におけるSafeState維持確認に成功。");

                match engine.state() {
                    VaultState::Unlocked => {
                        prop_assert!(engine.observe_dek().is_some());
                        prop_assert!(saw_valid_unlock, "有効な解錠を経ないUnlocked到達阻止の確認に成功。");
                    }
                    VaultState::Locked | VaultState::Unlocking | VaultState::Zeroized => {
                        prop_assert!(engine.observe_dek().is_none());
                    }
                }

                if prev_state == VaultState::Zeroized && ev != VaultEvent::Reset && res.is_err() {
                    prop_assert_eq!(engine.state(), VaultState::Zeroized);
                }
            }
        }

        #[test]
        fn prop_set_slots_guards_unlocking_state(
            initial_slots in arb_kek_slots(),
            new_slots in arb_kek_slots(),
            kind in prop_oneof![Just(SlotKind::Argon2id), Just(SlotKind::Prf), Just(SlotKind::Recovery)],
            new_status in arb_slot_status(),
            events in prop::collection::vec(arb_vault_event(), 0..16),
            dek_seed in any::<u8>(),
        ) {
            let mut engine = VaultEngine::new(initial_slots);
            for ev in events {
                let _ = match ev {
                    VaultEvent::StartUnlock(id) => engine.start_unlock(id),
                    VaultEvent::UnlockSuccess(id) => engine.complete_unlock(id, sample_dek(dek_seed)),
                    VaultEvent::UnlockFail => engine.fail_unlock(),
                    VaultEvent::Lock => engine.lock(),
                    VaultEvent::Zeroize => engine.zeroize_key(),
                    VaultEvent::Reset => engine.reset(),
                };
            }

            let state = engine.state();
            let prev_slots = *engine.slots();

            let res_slots = engine.set_slots(new_slots);
            let res_status = engine.set_slot_status(kind, new_status);

            if state == VaultState::Unlocking {
                prop_assert_eq!(res_slots, Err(VaultError::InvalidState), "Unlocking状態でのset_slots拒絶検証に成功。");
                prop_assert_eq!(res_status, Err(VaultError::InvalidState), "Unlocking状態でのset_slot_status拒絶検証に成功。");
                prop_assert_eq!(*engine.slots(), prev_slots, "拒絶時のスロット構成不変性の検証に成功。");
            } else {
                prop_assert_eq!(res_slots, Ok(()), "非Unlocking状態でのset_slots成功検証に成功。");
                prop_assert_eq!(res_status, Ok(()), "非Unlocking状態でのset_slot_status成功検証に成功。");
                prop_assert_eq!(engine.slots().status_of(kind), new_status, "スロット更新反映の検証に成功。");
            }
        }
    }
}
