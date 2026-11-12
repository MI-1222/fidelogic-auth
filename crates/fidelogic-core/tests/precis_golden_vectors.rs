//! # PRECIS ゴールデンテストベクタ結合テスト。
//!
//! 共通テストベクタ `tests/vectors/precis_golden_vectors.json` を走査し、
//! 形式仕様 `proofs/Theories/PrecisProfile.v` の Rocq モデルと
//! Rust 実装 (`crates/fidelogic-core/src/precis.rs`) との意味論的一致、
//! ならびに非許可コードポイント注入による変異拒絶を検証する。

#![cfg(feature = "alloc")]

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use fidelogic_core::{
    PrecisError, VaultError, all_allowed, all_opaque_allowed, enforce_opaque_string_cps,
    enforce_username_case_mapped_cps, opaque_string, precis_opaque_string,
    precis_username_case_mapped, username_case_mapped,
};

/// 外部依存なしで利用できる厳格な RFC 8259 準拠 JSON パーサー。
mod json_parser {
    use std::collections::BTreeMap;

    /// パース済み JSON 値を表す列挙型。
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum JsonValue {
        Null,
        Bool(bool),
        Int(i64),
        Str(String),
        Array(Vec<JsonValue>),
        Object(BTreeMap<String, JsonValue>),
    }

    impl JsonValue {
        /// オブジェクト参照を取得する。
        pub fn as_object(&self) -> Result<&BTreeMap<String, JsonValue>, String> {
            match self {
                Self::Object(map) => Ok(map),
                other => Err(format!("JSON object を期待しましたが {other:?} でした。")),
            }
        }

        /// 配列参照を取得する。
        pub fn as_array(&self) -> Result<&[JsonValue], String> {
            match self {
                Self::Array(items) => Ok(items.as_slice()),
                other => Err(format!("JSON array を期待しましたが {other:?} でした。")),
            }
        }

        /// 文字列参照を取得する。
        pub fn as_str(&self) -> Result<&str, String> {
            match self {
                Self::Str(s) => Ok(s.as_str()),
                other => Err(format!("JSON string を期待しましたが {other:?} でした。")),
            }
        }

        /// オプション文字列参照を取得する。
        pub fn as_opt_str(&self) -> Result<Option<&str>, String> {
            match self {
                Self::Null => Ok(None),
                Self::Str(s) => Ok(Some(s.as_str())),
                other => Err(format!(
                    "JSON string または null を期待しましたが {other:?} でした。"
                )),
            }
        }

        /// `u32` 整数値として取得する。
        pub fn as_u32(&self) -> Result<u32, String> {
            match self {
                Self::Int(v) => u32::try_from(*v)
                    .map_err(|_| format!("u32 範囲外の整数値が指定されました: {v}")),
                other => Err(format!("JSON integer を期待しましたが {other:?} でした。")),
            }
        }

        /// `usize` 整数値として取得する。
        pub fn as_usize(&self) -> Result<usize, String> {
            match self {
                Self::Int(v) => usize::try_from(*v)
                    .map_err(|_| format!("usize 範囲外の整数値が指定されました: {v}")),
                other => Err(format!("JSON integer を期待しましたが {other:?} でした。")),
            }
        }

        /// オブジェクトから必須フィールドを取得する。
        pub fn get<'a>(&'a self, key: &str) -> Result<&'a JsonValue, String> {
            let obj = self.as_object()?;
            obj.get(key)
                .ok_or_else(|| format!("必須キー '{key}' が JSON オブジェクトに存在しません。"))
        }

        /// オブジェクトから任意フィールドを取得する。
        pub fn get_opt<'a>(&'a self, key: &str) -> Result<Option<&'a JsonValue>, String> {
            let obj = self.as_object()?;
            Ok(obj.get(key))
        }
    }

    /// バイトスライス走査用のカーソル付き JSON デコーダ。
    struct Parser<'a> {
        src: &'a [u8],
        pos: usize,
    }

    impl<'a> Parser<'a> {
        fn new(input: &'a str) -> Self {
            Self {
                src: input.as_bytes(),
                pos: 0,
            }
        }

        fn skip_ws(&mut self) {
            while let Some(&b) = self.src.get(self.pos) {
                if matches!(b, b' ' | b'\t' | b'\r' | b'\n') {
                    self.pos += 1;
                } else {
                    break;
                }
            }
        }

        fn peek(&self) -> Option<u8> {
            self.src.get(self.pos).copied()
        }

        fn expect_byte(&mut self, expected: u8) -> Result<(), String> {
            match self.peek() {
                Some(b) if b == expected => {
                    self.pos += 1;
                    Ok(())
                }
                Some(b) => Err(format!(
                    "位置 {} で '{}' を期待しましたが '{}' が見つかりました。",
                    self.pos, expected as char, b as char
                )),
                None => Err(format!(
                    "位置 {} で '{}' を期待しましたが入力終端に到達しました。",
                    self.pos, expected as char
                )),
            }
        }

        fn expect_literal(&mut self, literal: &[u8]) -> Result<(), String> {
            let end = self.pos + literal.len();
            if self.src.get(self.pos..end) == Some(literal) {
                self.pos = end;
                Ok(())
            } else {
                Err(format!("位置 {} でリテラルが不正です。", self.pos))
            }
        }

        fn parse_value(&mut self) -> Result<JsonValue, String> {
            self.skip_ws();
            match self.peek() {
                Some(b'n') => {
                    self.expect_literal(b"null")?;
                    Ok(JsonValue::Null)
                }
                Some(b't') => {
                    self.expect_literal(b"true")?;
                    Ok(JsonValue::Bool(true))
                }
                Some(b'f') => {
                    self.expect_literal(b"false")?;
                    Ok(JsonValue::Bool(false))
                }
                Some(b'"') => self.parse_string().map(JsonValue::Str),
                Some(b'[') => self.parse_array(),
                Some(b'{') => self.parse_object(),
                Some(b'-') | Some(b'0'..=b'9') => self.parse_int().map(JsonValue::Int),
                Some(b) => Err(format!(
                    "位置 {} に予期しない文字 '{}' があります。",
                    self.pos, b as char
                )),
                None => Err("JSON 入力が予期せず終了しました。".to_string()),
            }
        }

        fn parse_hex4(&mut self) -> Result<u16, String> {
            let mut val: u16 = 0;
            for _ in 0..4 {
                let b = self
                    .peek()
                    .ok_or_else(|| "Unicode エスケープの途中で入力が終了しました。".to_string())?;
                self.pos += 1;
                let digit = match b {
                    b'0'..=b'9' => u16::from(b - b'0'),
                    b'a'..=b'f' => u16::from(b - b'a' + 10),
                    b'A'..=b'F' => u16::from(b - b'A' + 10),
                    _ => return Err(format!("不正な 16 進数字 '{}' です。", b as char)),
                };
                val = (val << 4) | digit;
            }
            Ok(val)
        }

        fn parse_string(&mut self) -> Result<String, String> {
            self.expect_byte(b'"')?;
            let mut out = String::new();

            loop {
                let b = self
                    .peek()
                    .ok_or_else(|| "閉じられていない JSON 文字列です。".to_string())?;
                if b == b'"' {
                    self.pos += 1;
                    return Ok(out);
                }
                if b == b'\\' {
                    self.pos += 1;
                    let esc = self
                        .peek()
                        .ok_or_else(|| "エスケープ文字の途中で入力が終了しました。".to_string())?;
                    self.pos += 1;
                    match esc {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{0008}'),
                        b'f' => out.push('\u{000C}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let first = self.parse_hex4()?;
                            if (0xD800..=0xDBFF).contains(&first) {
                                self.expect_byte(b'\\')?;
                                self.expect_byte(b'u')?;
                                let second = self.parse_hex4()?;
                                if !(0xDC00..=0xDFFF).contains(&second) {
                                    return Err(format!(
                                        "不正な下位サロゲート 0x{second:04X} です。"
                                    ));
                                }
                                let high = u32::from(first - 0xD800);
                                let low = u32::from(second - 0xDC00);
                                let cp = 0x1_0000 + ((high << 10) | low);
                                let ch = char::from_u32(cp)
                                    .ok_or_else(|| format!("不正なサロゲートペア U+{cp:X}"))?;
                                out.push(ch);
                            } else if (0xDC00..=0xDFFF).contains(&first) {
                                return Err(format!("孤立した下位サロゲート 0x{first:04X} です。"));
                            } else {
                                let ch = char::from_u32(u32::from(first))
                                    .ok_or_else(|| format!("不正なコードポイント 0x{first:04X}"))?;
                                out.push(ch);
                            }
                        }
                        other => {
                            return Err(format!(
                                "未対応のエスケープシーケンス '\\{}' です。",
                                other as char
                            ));
                        }
                    }
                } else if b < 0x20 {
                    return Err(format!("文字列内に生の制御文字 0x{b:02X} があります。"));
                } else {
                    let rest = std::str::from_utf8(&self.src[self.pos..])
                        .map_err(|err| format!("不正な UTF-8 バイト列: {err}"))?;
                    let ch = rest
                        .chars()
                        .next()
                        .ok_or_else(|| "文字列走査中に終端へ到達しました。".to_string())?;
                    out.push(ch);
                    self.pos += ch.len_utf8();
                }
            }
        }

        fn parse_int(&mut self) -> Result<i64, String> {
            let start = self.pos;
            if self.peek() == Some(b'-') {
                self.pos += 1;
            }
            let digits_start = self.pos;
            while let Some(b'0'..=b'9') = self.peek() {
                self.pos += 1;
            }
            if self.pos == digits_start {
                return Err(format!("位置 {start} の整数リテラルに数字がありません。"));
            }
            if matches!(self.peek(), Some(b'.' | b'e' | b'E')) {
                return Err(format!("位置 {} に非整数リテラルがあります。", self.pos));
            }
            let raw = std::str::from_utf8(&self.src[start..self.pos])
                .map_err(|err| format!("整数変換中の UTF-8 エラー: {err}"))?;
            raw.parse::<i64>()
                .map_err(|err| format!("整数 '{raw}' のパースに失敗しました: {err}"))
        }

        fn parse_array(&mut self) -> Result<JsonValue, String> {
            self.expect_byte(b'[')?;
            self.skip_ws();
            let mut items = Vec::new();
            if self.peek() == Some(b']') {
                self.pos += 1;
                return Ok(JsonValue::Array(items));
            }
            loop {
                items.push(self.parse_value()?);
                self.skip_ws();
                match self.peek() {
                    Some(b',') => {
                        self.pos += 1;
                    }
                    Some(b']') => {
                        self.pos += 1;
                        return Ok(JsonValue::Array(items));
                    }
                    _ => return Err(format!("位置 {} で ',' または ']' が必要です。", self.pos)),
                }
            }
        }

        fn parse_object(&mut self) -> Result<JsonValue, String> {
            self.expect_byte(b'{')?;
            self.skip_ws();
            let mut map = BTreeMap::new();
            if self.peek() == Some(b'}') {
                self.pos += 1;
                return Ok(JsonValue::Object(map));
            }
            loop {
                self.skip_ws();
                let key = self.parse_string()?;
                self.skip_ws();
                self.expect_byte(b':')?;
                let val = self.parse_value()?;
                if map.insert(key.clone(), val).is_some() {
                    return Err(format!("重複した JSON キー '{key}' が検出されました。"));
                }
                self.skip_ws();
                match self.peek() {
                    Some(b',') => {
                        self.pos += 1;
                    }
                    Some(b'}') => {
                        self.pos += 1;
                        return Ok(JsonValue::Object(map));
                    }
                    _ => return Err(format!("位置 {} で ',' または '}}' が必要です。", self.pos)),
                }
            }
        }
    }

    /// JSON 文字列全体をパースし、余剰トークンがないことを保証する。
    pub fn parse_json(input: &str) -> Result<JsonValue, String> {
        let mut parser = Parser::new(input);
        let value = parser.parse_value()?;
        parser.skip_ws();
        if parser.pos != parser.src.len() {
            return Err(format!(
                "JSON 終端以降の位置 {} に余剰データがあります。",
                parser.pos
            ));
        }
        Ok(value)
    }
}

use json_parser::{JsonValue, parse_json};

/// PRECIS 対象プロファイルの種別を表す列挙型。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProfileKind {
    UsernameCaseMapped,
    OpaqueString,
}

impl ProfileKind {
    /// デバッグ・アサーション表示用のプロファイル名。
    const fn label(self) -> &'static str {
        match self {
            Self::UsernameCaseMapped => "UsernameCaseMapped",
            Self::OpaqueString => "OpaqueString",
        }
    }

    /// コードポイント列に対する検証付き正規化 API を実行する。
    fn enforce_cps(self, cps: &[u32]) -> Result<Vec<u32>, PrecisError> {
        match self {
            Self::UsernameCaseMapped => enforce_username_case_mapped_cps(cps),
            Self::OpaqueString => enforce_opaque_string_cps(cps),
        }
    }

    /// Rocq モデルと同型の `Option` 返却正規化 API を実行する。
    fn precis_cps(self, cps: &[u32]) -> Option<Vec<u32>> {
        match self {
            Self::UsernameCaseMapped => precis_username_case_mapped(cps),
            Self::OpaqueString => precis_opaque_string(cps),
        }
    }

    /// UTF-8 文字列入力に対する正規化 API を実行する。
    fn enforce_str(self, input: &str) -> Result<String, PrecisError> {
        match self {
            Self::UsernameCaseMapped => username_case_mapped(input),
            Self::OpaqueString => opaque_string(input),
        }
    }

    /// 正規化後のコードポイント列が対象プロファイルの許可条件を満たすか判定する。
    fn all_allowed(self, cps: &[u32]) -> bool {
        match self {
            Self::UsernameCaseMapped => all_allowed(cps),
            Self::OpaqueString => all_opaque_allowed(cps),
        }
    }
}

/// JSON 内の期待エラー詳細。
#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedError {
    kind: String,
    codepoint: Option<u32>,
}

/// JSON 内の各プロファイル期待出力。
#[derive(Debug, Clone, PartialEq, Eq)]
struct ProfileExpectation {
    status: String,
    codepoints: Option<Vec<u32>>,
    utf8: Option<String>,
    error: Option<ExpectedError>,
}

/// JSON ゴールデンテストベクタ 1 件分の構造体。
#[derive(Debug, Clone, PartialEq, Eq)]
struct GoldenVector {
    id: String,
    category: String,
    source: String,
    input_codepoints: Vec<u32>,
    input_utf8: Option<String>,
    username_case_mapped: ProfileExpectation,
    opaque_string: ProfileExpectation,
    rocq_suite_index: Option<usize>,
}

/// JSON ゴールデンテストスイート全体。
#[derive(Debug, Clone, PartialEq, Eq)]
struct GoldenSuite {
    schema_version: String,
    formal_model: String,
    rust_implementation: String,
    vector_count: usize,
    vectors: Vec<GoldenVector>,
    rfc_extended_count: usize,
}

/// Rocq `PrecisProfile.v` 内の `PrecisTestCase` レコード。
#[derive(Debug, Clone, PartialEq, Eq)]
struct RocqTestCase {
    input: Vec<u32>,
    expected_user: Option<Vec<u32>>,
    expected_opaque: Option<Vec<u32>>,
}

/// JSON 配列から `u32` コードポイント列をデコードする。
fn decode_u32_array(val: &JsonValue) -> Result<Vec<u32>, String> {
    let arr = val.as_array()?;
    arr.iter().map(JsonValue::as_u32).collect()
}

/// JSON オブジェクトからプロファイル期待結果をデコードする。
fn decode_profile_expectation(val: &JsonValue) -> Result<ProfileExpectation, String> {
    let status = val.get("status")?.as_str()?.to_string();
    let codepoints = match val.get("codepoints")? {
        JsonValue::Null => None,
        other => Some(decode_u32_array(other)?),
    };
    let utf8 = val.get("utf8")?.as_opt_str()?.map(str::to_string);
    let error = match val.get("error")? {
        JsonValue::Null => None,
        err_val => {
            let kind = err_val.get("kind")?.as_str()?.to_string();
            let codepoint = match err_val.get_opt("codepoint")? {
                None | Some(JsonValue::Null) => None,
                Some(cp_val) => Some(cp_val.as_u32()?),
            };
            Some(ExpectedError { kind, codepoint })
        }
    };

    Ok(ProfileExpectation {
        status,
        codepoints,
        utf8,
        error,
    })
}

/// `tests/vectors/precis_golden_vectors.json` を読み込み構造化する。
fn load_golden_suite() -> GoldenSuite {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/vectors/precis_golden_vectors.json");
    let raw = fs::read_to_string(&path).unwrap_or_else(|err| {
        panic!("ゴールデンベクタ JSON の読み込みに失敗しました ({path:?}): {err}")
    });
    let root = parse_json(&raw)
        .unwrap_or_else(|err| panic!("ゴールデンベクタ JSON のパースに失敗しました: {err}"));

    let schema_version = root
        .get("schema_version")
        .unwrap()
        .as_str()
        .unwrap()
        .to_string();
    let formal_model = root
        .get("formal_model")
        .unwrap()
        .as_str()
        .unwrap()
        .to_string();
    let rust_implementation = root
        .get("rust_implementation")
        .unwrap()
        .as_str()
        .unwrap()
        .to_string();
    let vector_count = root.get("vector_count").unwrap().as_usize().unwrap();
    let raw_vectors = root.get("vectors").unwrap().as_array().unwrap();
    let rfc_extended_count = root
        .get("rfc_extended_reference_vectors")
        .unwrap()
        .as_array()
        .unwrap()
        .len();

    let mut vectors = Vec::with_capacity(raw_vectors.len());
    for entry in raw_vectors {
        let id = entry.get("id").unwrap().as_str().unwrap().to_string();
        let category = entry.get("category").unwrap().as_str().unwrap().to_string();
        let source = entry.get("source").unwrap().as_str().unwrap().to_string();
        let input_obj = entry.get("input").unwrap();
        let input_codepoints = decode_u32_array(input_obj.get("codepoints").unwrap()).unwrap();
        let input_utf8 = input_obj
            .get("utf8")
            .unwrap()
            .as_opt_str()
            .unwrap()
            .map(str::to_string);
        let username_case_mapped =
            decode_profile_expectation(entry.get("username_case_mapped").unwrap()).unwrap();
        let opaque_string =
            decode_profile_expectation(entry.get("opaque_string").unwrap()).unwrap();
        let rocq_suite_index = entry
            .get_opt("rocq_suite_index")
            .unwrap()
            .map(|v| v.as_usize().unwrap());

        vectors.push(GoldenVector {
            id,
            category,
            source,
            input_codepoints,
            input_utf8,
            username_case_mapped,
            opaque_string,
            rocq_suite_index,
        });
    }

    GoldenSuite {
        schema_version,
        formal_model,
        rust_implementation,
        vector_count,
        vectors,
        rfc_extended_count,
    }
}

/// コードポイント列を UTF-8 文字列へ変換する。
fn codepoints_to_utf8(cps: &[u32]) -> Result<String, String> {
    let mut out = String::with_capacity(cps.len());
    for &cp in cps {
        let ch = char::from_u32(cp).ok_or_else(|| format!("非スカラコードポイント U+{cp:X}"))?;
        out.push(ch);
    }
    Ok(out)
}

/// Rocq リストリテラル `[a; b; c]` を `Vec<u32>` にパースする。
fn parse_rocq_u32_list(raw: &str) -> Result<Vec<u32>, String> {
    let trimmed = raw.trim();
    let inner = trimmed
        .strip_prefix('[')
        .and_then(|s| s.strip_suffix(']'))
        .ok_or_else(|| format!("Rocq リストリテラルが不正です: '{trimmed}'"))?
        .trim();
    if inner.is_empty() {
        return Ok(Vec::new());
    }
    inner
        .split(';')
        .map(|part| {
            part.trim()
                .parse::<u32>()
                .map_err(|err| format!("Rocq 整数要素 '{}' のパースに失敗: {err}", part.trim()))
        })
        .collect()
}

/// Rocq `option PrecisString` リテラル (`None` または `Some [...]`) をパースする。
fn parse_rocq_option_list(raw: &str) -> Result<Option<Vec<u32>>, String> {
    let trimmed = raw.trim();
    if trimmed == "None" {
        return Ok(None);
    }
    if let Some(rest) = trimmed.strip_prefix("Some") {
        return parse_rocq_u32_list(rest).map(Some);
    }
    Err(format!("Rocq option リテラルが不正です: '{trimmed}'"))
}

/// `proofs/Theories/PrecisProfile.v` から `precis_golden_suite` 全レコードを抽出する。
fn load_rocq_golden_suite() -> Vec<RocqTestCase> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/Theories/PrecisProfile.v");
    let source = fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("PrecisProfile.v の読み込みに失敗しました ({path:?}): {err}"));

    assert!(
        source.contains("Theorem precis_golden_suite_conformance"),
        "PrecisProfile.v に precis_golden_suite_conformance 定理が存在することを確認。"
    );

    let marker = "Definition precis_golden_suite : list PrecisTestCase := [";
    let start = source
        .find(marker)
        .expect("PrecisProfile.v に precis_golden_suite 定義が存在することを確認。")
        + marker.len();
    let body_and_tail = &source[start..];
    let end = body_and_tail
        .find("\n].")
        .expect("precis_golden_suite 定義の終端 '].' が存在することを確認。");
    let body = &body_and_tail[..end];

    let mut cases = Vec::new();
    let mut cursor = body;
    while let Some(rec_start) = cursor.find("{|") {
        let after_start = &cursor[rec_start + 2..];
        let rec_end = after_start
            .find("|}")
            .expect("PrecisTestCase レコードの終端 '|}' が存在することを確認。");
        let rec = &after_start[..rec_end];
        cursor = &after_start[rec_end + 2..];

        // セミコロンはリストリテラル内部にも出現するため、フィールド名で分割する。
        let user_pos = rec
            .find("tc_expected_user :=")
            .expect("tc_expected_user フィールドの存在を確認。");
        let opaque_pos = rec
            .find("tc_expected_opaque :=")
            .expect("tc_expected_opaque フィールドの存在を確認。");
        let input_pos = rec
            .find("tc_input :=")
            .expect("tc_input フィールドの存在を確認。");

        assert!(input_pos < user_pos && user_pos < opaque_pos);

        let input_raw = rec[input_pos + "tc_input :=".len()..user_pos]
            .trim()
            .trim_end_matches(';');
        let user_raw = rec[user_pos + "tc_expected_user :=".len()..opaque_pos]
            .trim()
            .trim_end_matches(';');
        let opaque_raw = rec[opaque_pos + "tc_expected_opaque :=".len()..].trim();

        cases.push(RocqTestCase {
            input: parse_rocq_u32_list(input_raw).unwrap(),
            expected_user: parse_rocq_option_list(user_raw).unwrap(),
            expected_opaque: parse_rocq_option_list(opaque_raw).unwrap(),
        });
    }

    cases
}

/// 期待エラー定義を [`PrecisError`] へ変換する。
fn expected_err_to_precis_error(err: &ExpectedError) -> PrecisError {
    match err.kind.as_str() {
        "EmptyInput" => PrecisError::EmptyInput,
        "DisallowedCodePoint" => PrecisError::DisallowedCodePoint(
            err.codepoint
                .expect("DisallowedCodePoint エラーには codepoint フィールドが必要です。"),
        ),
        other => panic!("未知のエラー種別です: {other}"),
    }
}

/// 単一ベクタ・単一プロファイルについて Rust 実装と期待値の完全一致を検証する。
fn verify_profile_expectation(vec: &GoldenVector, profile: ProfileKind, exp: &ProfileExpectation) {
    let label = profile.label();
    let actual_cps_res = profile.enforce_cps(&vec.input_codepoints);
    let actual_opt = profile.precis_cps(&vec.input_codepoints);

    match exp.status.as_str() {
        "ok" => {
            let expected_cps = exp.codepoints.as_ref().unwrap_or_else(|| {
                panic!("[{}: {label}] status=ok だが codepoints が null。", vec.id)
            });
            let expected_utf8 = exp
                .utf8
                .as_ref()
                .unwrap_or_else(|| panic!("[{}: {label}] status=ok だが utf8 が null。", vec.id));
            assert!(
                exp.error.is_none(),
                "[{}: {label}] status=ok だが error が非 null。",
                vec.id
            );

            assert_eq!(
                actual_cps_res.as_ref(),
                Ok(expected_cps),
                "[{}: {label}] enforce_*_cps の結果が期待値と一致しません。",
                vec.id
            );
            assert_eq!(
                actual_opt.as_ref(),
                Some(expected_cps),
                "[{}: {label}] precis_* の結果が期待値と一致しません。",
                vec.id
            );
            assert!(
                profile.all_allowed(expected_cps),
                "[{}: {label}] 正規化後コードポイント列に非許可文字が含まれています。",
                vec.id
            );

            let rendered_utf8 = codepoints_to_utf8(expected_cps)
                .unwrap_or_else(|err| panic!("[{}: {label}] UTF-8 変換失敗: {err}", vec.id));
            assert_eq!(
                &rendered_utf8, expected_utf8,
                "[{}: {label}] 期待コードポイント列と期待 UTF-8 文字列が整合しません。",
                vec.id
            );

            // 冪等性: 正規化済み出力への再適用が恒等写像であることを検証する。
            assert_eq!(
                profile.enforce_cps(expected_cps).as_ref(),
                Ok(expected_cps),
                "[{}: {label}] コードポイント列 API が冪等ではありません。",
                vec.id
            );
            assert_eq!(
                profile.precis_cps(expected_cps).as_ref(),
                Some(expected_cps),
                "[{}: {label}] Option 返却 API が冪等ではありません。",
                vec.id
            );

            if let Some(ref input_str) = vec.input_utf8 {
                assert_eq!(
                    profile.enforce_str(input_str).as_ref(),
                    Ok(expected_utf8),
                    "[{}: {label}] UTF-8 文字列 API の結果が期待値と一致しません。",
                    vec.id
                );
                assert_eq!(
                    profile.enforce_str(expected_utf8).as_ref(),
                    Ok(expected_utf8),
                    "[{}: {label}] UTF-8 文字列 API が冪等ではありません。",
                    vec.id
                );
            }
        }
        "err" => {
            assert!(
                exp.codepoints.is_none() && exp.utf8.is_none(),
                "[{}: {label}] status=err だが期待出力が null ではありません。",
                vec.id
            );
            let exp_err = exp
                .error
                .as_ref()
                .unwrap_or_else(|| panic!("[{}: {label}] status=err だが error が null。", vec.id));
            let expected_precis_err = expected_err_to_precis_error(exp_err);

            assert_eq!(
                actual_cps_res,
                Err(expected_precis_err),
                "[{}: {label}] enforce_*_cps の拒絶エラーが期待値と一致しません。",
                vec.id
            );
            assert_eq!(
                actual_opt, None,
                "[{}: {label}] precis_* は拒絶時に None を返す必要があります。",
                vec.id
            );

            // Vault 境界のエラーマスキングとも整合することを確認する。
            assert_eq!(
                VaultError::from(expected_precis_err).mask_auth_error(),
                VaultError::AuthenticationFailed,
                "[{}: {label}] PrecisError が境界で一様認証失敗へマスクされることを確認。",
                vec.id
            );

            if let Some(ref input_str) = vec.input_utf8 {
                assert_eq!(
                    profile.enforce_str(input_str),
                    Err(expected_precis_err),
                    "[{}: {label}] UTF-8 文字列 API の拒絶エラーが期待値と一致しません。",
                    vec.id
                );
            }
        }
        other => panic!("[{}: {label}] 未知の status '{other}' です。", vec.id),
    }
}

/// コードポイント列の位置 (先頭・中央・末尾) に指定コードポイントを挿入した変異列を生成する。
fn inject_codepoint_at(base: &[u32], pos: usize, injected: u32) -> Vec<u32> {
    let mut mutated = Vec::with_capacity(base.len() + 1);
    mutated.extend_from_slice(&base[..pos]);
    mutated.push(injected);
    mutated.extend_from_slice(&base[pos..]);
    mutated
}

#[test]
fn test_json_parser_roundtrip_and_escapes() {
    let sample = r#"{
        "schema": "1.0.0",
        "nums": [0, 85, 1114112],
        "unicode": "e\u0301 \uD83D\uDD11",
        "flag": true,
        "empty": null
    }"#;
    let parsed = parse_json(sample).expect("正当な JSON のパースに成功。");
    assert_eq!(parsed.get("schema").unwrap().as_str().unwrap(), "1.0.0");
    assert_eq!(
        parsed.get("unicode").unwrap().as_str().unwrap(),
        "e\u{0301} \u{1F511}"
    );
    assert_eq!(
        decode_u32_array(parsed.get("nums").unwrap()).unwrap(),
        vec![0, 85, 1_114_112]
    );
    assert!(parse_json("{invalid}").is_err());
    assert!(parse_json("123 trailing").is_err());
}

#[test]
fn test_json_golden_suite_all_124_vectors() {
    let suite = load_golden_suite();

    assert_eq!(suite.schema_version, "1.0.0");
    assert_eq!(suite.formal_model, "proofs/Theories/PrecisProfile.v");
    assert_eq!(
        suite.rust_implementation,
        "crates/fidelogic-core/src/precis.rs"
    );
    assert_eq!(suite.vector_count, 124);
    assert_eq!(suite.vectors.len(), suite.vector_count);
    assert_eq!(suite.rfc_extended_count, 4);

    let mut seen_ids = BTreeSet::new();
    let mut category_counts: BTreeMap<String, usize> = BTreeMap::new();

    for vec in &suite.vectors {
        assert!(
            !vec.id.is_empty(),
            "テストベクタ ID は空であってはなりません。"
        );
        assert!(
            !vec.source.is_empty(),
            "source メタデータは空であってはなりません。"
        );
        assert!(
            seen_ids.insert(vec.id.clone()),
            "重複したテストベクタ ID '{}' が存在します。",
            vec.id
        );
        *category_counts.entry(vec.category.clone()).or_insert(0) += 1;

        // JSON 内の input.codepoints と input.utf8 の相互整合性を検証する。
        match &vec.input_utf8 {
            Some(input_str) => {
                let decoded_cps: Vec<u32> = input_str.chars().map(|ch| ch as u32).collect();
                assert_eq!(
                    decoded_cps, vec.input_codepoints,
                    "[{}] input.utf8 と input.codepoints が一致しません。",
                    vec.id
                );
            }
            None => {
                assert!(
                    vec.input_codepoints
                        .iter()
                        .any(|&cp| char::from_u32(cp).is_none()),
                    "[{}] input.utf8 が null なのに非スカラ値を含みません。",
                    vec.id
                );
            }
        }

        verify_profile_expectation(
            vec,
            ProfileKind::UsernameCaseMapped,
            &vec.username_case_mapped,
        );
        verify_profile_expectation(vec, ProfileKind::OpaqueString, &vec.opaque_string);
    }

    for required_category in [
        "case_folding",
        "profile_discrepancy",
        "disallowed_empty",
        "disallowed_control",
        "disallowed_surrogate",
        "disallowed_pua",
        "disallowed_noncharacter",
        "combining_nfc",
        "hangul_nfc",
        "rfc8265_appendix",
        "boundary_preserved",
        "disallowed_space",
        "disallowed_out_of_bounds",
        "mutation_rejection",
    ] {
        assert!(
            category_counts.get(required_category).copied().unwrap_or(0) >= 1,
            "必須カテゴリ '{required_category}' がゴールデンテストスイートに含まれていることを確認。"
        );
    }
}

#[test]
fn test_rocq_precis_golden_suite_semantic_equivalence() {
    let json_suite = load_golden_suite();
    let rocq_cases = load_rocq_golden_suite();

    assert_eq!(
        rocq_cases.len(),
        20,
        "PrecisProfile.v の precis_golden_suite は全 20 件であることを確認。"
    );

    let mut matched_indices = BTreeSet::new();
    for (idx, rocq_case) in rocq_cases.iter().enumerate() {
        let json_vec = json_suite
            .vectors
            .iter()
            .find(|v| v.rocq_suite_index == Some(idx))
            .unwrap_or_else(|| {
                panic!("JSON スイート内に rocq_suite_index={idx} の対応ベクタが存在しません。")
            });
        matched_indices.insert(idx);

        // 1. Rocq モデルと JSON ベクタの入力・期待値が一致することを検証する。
        assert_eq!(
            json_vec.input_codepoints, rocq_case.input,
            "rocq_suite_index={idx} ({}) の入力列が Rocq と一致しません。",
            json_vec.id
        );
        assert_eq!(
            json_vec.username_case_mapped.codepoints, rocq_case.expected_user,
            "rocq_suite_index={idx} ({}) の UsernameCaseMapped 期待値が Rocq と一致しません。",
            json_vec.id
        );
        assert_eq!(
            json_vec.opaque_string.codepoints, rocq_case.expected_opaque,
            "rocq_suite_index={idx} ({}) の OpaqueString 期待値が Rocq と一致しません。",
            json_vec.id
        );

        // 2. Rocq モデルの期待結果と Rust 実装の出力が完全に意味論一致することを検証する。
        assert_eq!(
            precis_username_case_mapped(&rocq_case.input),
            rocq_case.expected_user,
            "rocq_suite_index={idx} で Rocq モデルと Rust 実装 (UsernameCaseMapped) が不一致。",
        );
        assert_eq!(
            precis_opaque_string(&rocq_case.input),
            rocq_case.expected_opaque,
            "rocq_suite_index={idx} で Rocq モデルと Rust 実装 (OpaqueString) が不一致。",
        );
    }

    assert_eq!(matched_indices.len(), 20);
}

#[test]
fn test_disallowed_codepoint_mutation_rejection() {
    let suite = load_golden_suite();

    // IdentifierClass / FreeformClass 双方で禁止される全領域の境界変異コードポイント群。
    let common_disallowed_cps: &[u32] = &[
        0x0000,    // ASCII NUL.
        0x0001,    // ASCII SOH.
        0x0009,    // TAB.
        0x000A,    // LF.
        0x000D,    // CR.
        0x001F,    // ASCII 制御文字上限.
        0x007F,    // DEL.
        0x0080,    // C1 制御文字下限.
        0x0085,    // NEL.
        0x009F,    // C1 制御文字上限.
        0xD800,    // 上位サロゲート下限.
        0xDBFF,    // 上位サロゲート上限.
        0xDC00,    // 下位サロゲート下限.
        0xDFFF,    // 下位サロゲート上限.
        0xE000,    // BMP 私用領域下限.
        0xF8FF,    // BMP 私用領域上限.
        0xF_0000,  // Plane 15 私用領域下限.
        0xF_FFFD,  // Plane 15 私用領域上限.
        0x10_0000, // Plane 16 私用領域下限.
        0x10_FFFD, // Plane 16 私用領域上限.
        0xFDD0,    // 非文字ブロック下限.
        0xFDEF,    // 非文字ブロック上限.
        0xFFFE,    // BMP 末尾非文字.
        0xFFFF,    // BMP 末尾非文字.
        0x1_FFFE,  // Plane 1 末尾非文字.
        0x1_FFFF,  // Plane 1 末尾非文字.
        0x10_FFFE, // Unicode 最大面末尾非文字.
        0x10_FFFF, // Unicode 最大コードポイント兼非文字.
        0x11_0000, // Unicode 有効範囲外下限.
        u32::MAX,  // u32 最大範囲外値.
    ];

    let mut username_mutation_checks = 0usize;
    let mut opaque_mutation_checks = 0usize;

    for vec in &suite.vectors {
        let len = vec.input_codepoints.len();
        let positions = [0, len / 2, len];

        // 1. UsernameCaseMapped で受理される全ベクタに対し、共通禁止文字および ASCII 空白 (0x20) の変異拒絶を検証する。
        if vec.username_case_mapped.status == "ok" {
            for &bad_cp in common_disallowed_cps
                .iter()
                .chain(core::iter::once(&0x0020))
            {
                for pos in positions {
                    let mutated = inject_codepoint_at(&vec.input_codepoints, pos, bad_cp);
                    assert_eq!(
                        enforce_username_case_mapped_cps(&mutated),
                        Err(PrecisError::DisallowedCodePoint(bad_cp)),
                        "[{}] UsernameCaseMapped が変異コードポイント U+{bad_cp:04X} (pos={pos}) を拒絶しませんでした。",
                        vec.id
                    );
                    assert_eq!(
                        precis_username_case_mapped(&mutated),
                        None,
                        "[{}] precis_username_case_mapped が変異に対して None を返しませんでした。",
                        vec.id
                    );

                    if let Some(ch) = char::from_u32(bad_cp) {
                        let mutated_str = codepoints_to_utf8(&mutated).unwrap();
                        assert_eq!(
                            username_case_mapped(&mutated_str),
                            Err(PrecisError::DisallowedCodePoint(bad_cp)),
                            "[{}] UTF-8 変異 '{ch:?}' (U+{bad_cp:04X}, pos={pos}) の拒絶に失敗しました。",
                            vec.id
                        );
                    }
                    username_mutation_checks += 1;
                }
            }
        }

        // 2. OpaqueString で受理される全ベクタに対し、共通禁止文字の変異拒絶と ASCII 空白 (0x20) 許容境界を検証する。
        if vec.opaque_string.status == "ok" {
            for &bad_cp in common_disallowed_cps {
                for pos in positions {
                    let mutated = inject_codepoint_at(&vec.input_codepoints, pos, bad_cp);
                    assert_eq!(
                        enforce_opaque_string_cps(&mutated),
                        Err(PrecisError::DisallowedCodePoint(bad_cp)),
                        "[{}] OpaqueString が変異コードポイント U+{bad_cp:04X} (pos={pos}) を拒絶しませんでした。",
                        vec.id
                    );
                    assert_eq!(
                        precis_opaque_string(&mutated),
                        None,
                        "[{}] precis_opaque_string が変異に対して None を返しませんでした。",
                        vec.id
                    );

                    if char::from_u32(bad_cp).is_some() {
                        let mutated_str = codepoints_to_utf8(&mutated).unwrap();
                        assert_eq!(
                            opaque_string(&mutated_str),
                            Err(PrecisError::DisallowedCodePoint(bad_cp)),
                            "[{}] UTF-8 変異 (U+{bad_cp:04X}, pos={pos}) の拒絶に失敗しました。",
                            vec.id
                        );
                    }
                    opaque_mutation_checks += 1;
                }
            }

            // ASCII 空白 (0x20) の注入は OpaqueString (FreeformClass) では許可・保持されることを検証する。
            for pos in positions {
                let with_space = inject_codepoint_at(&vec.input_codepoints, pos, 0x0020);
                let normalized = enforce_opaque_string_cps(&with_space).unwrap_or_else(|err| {
                    panic!(
                        "[{}] OpaqueString は ASCII 空白注入 (pos={pos}) を許可すべきですが {err:?} となりました。",
                        vec.id
                    )
                });
                assert!(all_opaque_allowed(&normalized));
                assert_eq!(precis_opaque_string(&normalized), Some(normalized.clone()));
            }
        }
    }

    assert!(
        username_mutation_checks > 5_000,
        "UsernameCaseMapped の変異拒絶テストが十分数実行されたことを確認 ({username_mutation_checks} 件)。"
    );
    assert!(
        opaque_mutation_checks > 5_000,
        "OpaqueString の変異拒絶テストが十分数実行されたことを確認 ({opaque_mutation_checks} 件)。"
    );
}

#[cfg(feature = "profile-lite")]
#[test]
fn test_profile_lite_precis_golden_reexports() {
    use fidelogic_core::profile_lite;

    let suite = load_golden_suite();
    for vec in suite.vectors.iter().take(20) {
        assert_eq!(
            profile_lite::precis_username_case_mapped(&vec.input_codepoints),
            precis_username_case_mapped(&vec.input_codepoints),
            "[{}] profile_lite 再エクスポート (UsernameCaseMapped) が一致することを確認。",
            vec.id
        );
        assert_eq!(
            profile_lite::precis_opaque_string(&vec.input_codepoints),
            precis_opaque_string(&vec.input_codepoints),
            "[{}] profile_lite 再エクスポート (OpaqueString) が一致することを確認。",
            vec.id
        );
    }
}

#[cfg(feature = "profile-vault")]
#[test]
fn test_profile_vault_precis_golden_reexports() {
    use fidelogic_core::profile_vault;

    let suite = load_golden_suite();
    for vec in suite.vectors.iter().take(20) {
        assert_eq!(
            profile_vault::precis_username_case_mapped(&vec.input_codepoints),
            precis_username_case_mapped(&vec.input_codepoints),
            "[{}] profile_vault 再エクスポート (UsernameCaseMapped) が一致することを確認。",
            vec.id
        );
        assert_eq!(
            profile_vault::precis_opaque_string(&vec.input_codepoints),
            precis_opaque_string(&vec.input_codepoints),
            "[{}] profile_vault 再エクスポート (OpaqueString) が一致することを確認。",
            vec.id
        );
    }
}
