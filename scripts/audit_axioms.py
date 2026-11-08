#!/usr/bin/env python3
"""Axiom soundness and kernel assumption audit script for Rocq and Coq theorems.

Executes 'Print Assumptions' in an isolated REPL subprocess and strictly
verifies the kernel's CONTEXT SUMMARY or legacy Axioms block.
Detects unapproved axioms, unfinished proofs (Admitted / admit),
and disabled kernel safety mechanisms.
"""

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
from typing import Any

# Standard approved axioms recognized across Software Foundations (LF/PLF/VFA) and Coq/Rocq standard libraries.
STANDARD_APPROVED_AXIOMS: set[str] = {
    # Functional Extensionality
    "Coq.Logic.FunctionalExtensionality.functional_extensionality_dep",
    "Coq.Logic.FunctionalExtensionality.functional_extensionality",
    "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep",
    "Stdlib.Logic.FunctionalExtensionality.functional_extensionality",
    "FunctionalExtensionality.functional_extensionality_dep",
    "FunctionalExtensionality.functional_extensionality",
    "functional_extensionality_dep",
    "functional_extensionality",
    # Proof Irrelevance
    "Coq.Logic.ProofIrrelevance.proof_irrelevance",
    "Stdlib.Logic.ProofIrrelevance.proof_irrelevance",
    "ProofIrrelevance.proof_irrelevance",
    "proof_irrelevance",
    # Law of Excluded Middle / Classical Logic
    "Coq.Logic.Classical_Prop.classic",
    "Stdlib.Logic.Classical_Prop.classic",
    "Classical.classic",
    "classic",
    # Classical Real Analysis / Dedekind Reals
    "Coq.Reals.ClassicalDedekindReals.sig_forall_dec",
    "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec",
    "ClassicalDedekindReals.sig_forall_dec",
    "sig_forall_dec",
    "Coq.Reals.ClassicalConstructiveReals.sig_forall_dec",
    "Stdlib.Reals.ClassicalConstructiveReals.sig_forall_dec",
    "ClassicalConstructiveReals.sig_forall_dec",
}

# Approved axioms for TLC library in Separation Logic Foundations (SLF).

# Approved axioms for Aeneas pure modeling primitives (slice, array, and arch-specific scalar bounds).
AENEAS_APPROVED_AXIOMS: set[str] = {
    "Primitives.Primitives.isize_min",
    "Primitives.Primitives.isize_max",
    "Primitives.Primitives.usize_max",
    "Primitives.Primitives.isize_min_bound",
    "Primitives.Primitives.isize_max_bound",
    "Primitives.Primitives.usize_max_bound",
    "Primitives.isize_min",
    "Primitives.isize_max",
    "Primitives.usize_max",
    "Primitives.isize_min_bound",
    "Primitives.isize_max_bound",
    "Primitives.usize_max_bound",
    "isize_min",
    "isize_max",
    "usize_max",
    "isize_min_bound",
    "isize_max_bound",
    "usize_max_bound",
    "Primitives.Primitives.slice_len",
    "Primitives.Primitives.slice_index_usize",
    "Primitives.Primitives.slice_update_usize",
    "Primitives.Primitives.slice_update",
    "Primitives.slice_len",
    "Primitives.slice_index_usize",
    "Primitives.slice_update_usize",
    "Primitives.slice_update",
    "slice_len",
    "slice_index_usize",
    "slice_update_usize",
    "slice_update",
    "Primitives.Primitives.mk_array",
    "Primitives.Primitives.array_repeat",
    "Primitives.Primitives.array_index_usize",
    "Primitives.Primitives.array_update_usize",
    "Primitives.Primitives.array_update",
    "Primitives.Primitives.array_to_slice",
    "Primitives.Primitives.array_from_slice",
    "Primitives.Primitives.array_to_slice_len",
    "Primitives.Primitives.array_to_slice_index",
    "Primitives.Primitives.mk_array_index_nth",
    "Primitives.array_to_slice_len",
    "Primitives.array_to_slice_index",
    "Primitives.mk_array_index_nth",
    "array_to_slice_len",
    "array_to_slice_index",
    "mk_array_index_nth",
    "TlvRoundtrip.TlvRoundtrip.array_to_slice_range_from_end",
    "TlvRoundtrip.array_to_slice_range_from_end",
    "array_to_slice_range_from_end",
    "Primitives.Primitives.alloc_vec_Vec_index_usize",
    "Primitives.Primitives.alloc_vec_Vec_update_usize",
    "Primitives.Primitives.alloc_vec_Vec_update",
    # Range and Slice indexing primitives
    "Primitives.Primitives.core_slice_index_SliceIndexRangeToUsizeSlice_get",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeToUsizeSlice_get_mut",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeToUsizeSlice_index",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeToUsizeSlice_index_mut",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeFromUsizeSlice_get",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeFromUsizeSlice_get_mut",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeFromUsizeSlice_index",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeFromUsizeSlice_index_mut",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeUsizeSlice_get",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeUsizeSlice_get_mut",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeUsizeSlice_index",
    "Primitives.Primitives.core_slice_index_SliceIndexRangeUsizeSlice_index_mut",
    "core_slice_index_SliceIndexRangeToUsizeSlice_get",
    "core_slice_index_SliceIndexRangeToUsizeSlice_get_mut",
    "core_slice_index_SliceIndexRangeToUsizeSlice_index",
    "core_slice_index_SliceIndexRangeToUsizeSlice_index_mut",
    "core_slice_index_SliceIndexRangeFromUsizeSlice_get",
    "core_slice_index_SliceIndexRangeFromUsizeSlice_get_mut",
    "core_slice_index_SliceIndexRangeFromUsizeSlice_index",
    "core_slice_index_SliceIndexRangeFromUsizeSlice_index_mut",
    "core_slice_index_SliceIndexRangeUsizeSlice_get",
    "core_slice_index_SliceIndexRangeUsizeSlice_get_mut",
    "core_slice_index_SliceIndexRangeUsizeSlice_index",
    "core_slice_index_SliceIndexRangeUsizeSlice_index_mut",
    # Range trait implementations
    "FidelogicCore.FidelogicCore.core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_index",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut",
    "core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_index",
    "core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut",
    "core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get",
    "core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut",
    "core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked",
    "core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_index",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked",
    "FidelogicCore.FidelogicCore.core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut",
    "core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_index",
    "core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_index_mut",
    "core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get",
    "core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_mut",
    "core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked",
    "core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice_get_unchecked_mut",
    # Slice and Vec conversion primitives
    "FidelogicCore.FidelogicCore.core_slice_Slice_copy_from_slice",
    "core_slice_Slice_copy_from_slice",
    "FidelogicCore.FidelogicCore.alloc_vec_Vec_Insts_CoreConvertFromShared0Slice_from",
    "alloc_vec_Vec_Insts_CoreConvertFromShared0Slice_from",
}

TLC_APPROVED_AXIOMS: set[str] = {
    "LibAxioms.prop_ext",
    "LibAxioms.fun_ext_dep",
    "LibAxioms.classicT",
    "TLC.LibAxioms.prop_ext",
    "TLC.LibAxioms.fun_ext_dep",
    "TLC.LibAxioms.classic",
    "TLC.LibAxioms.classicT",
    "TLC.LibAxioms.indefinite_description",
}


def load_project_arguments(project_dir: str) -> list[str]:
    """Extract compiler options and logical path mappings from _RocqProject or _CoqProject.

    Args:
        project_dir: Root directory of the project.

    Returns:
        List of command-line arguments to pass to the REPL.
    """
    rocq_path = os.path.join(project_dir, "_RocqProject")
    coq_path = os.path.join(project_dir, "_CoqProject")

    if os.path.isfile(rocq_path):
        project_file_path = rocq_path
    elif os.path.isfile(coq_path):
        project_file_path = coq_path
    else:
        return []

    collected_arguments: list[str] = []
    try:
        with open(project_file_path, "r", encoding="utf-8") as file_handle:
            lines = file_handle.readlines()
    except OSError:
        return []

    for line in lines:
        stripped_line = line.strip()
        if not stripped_line or stripped_line.startswith("#"):
            continue

        tokens = shlex.split(stripped_line, comments=True)
        idx = 0
        while idx < len(tokens):
            token = tokens[idx]
            if token in ("-Q", "-R"):
                if idx + 2 < len(tokens):
                    physical_path = os.path.abspath(
                        os.path.join(project_dir, tokens[idx + 1])
                    )
                    logical_prefix = tokens[idx + 2]
                    collected_arguments.extend([token, physical_path, logical_prefix])
                    idx += 3
                else:
                    idx += 1
            elif token == "-I":
                if idx + 1 < len(tokens):
                    include_path = os.path.abspath(
                        os.path.join(project_dir, tokens[idx + 1])
                    )
                    collected_arguments.extend(["-I", include_path])
                    idx += 2
                else:
                    idx += 1
            elif token == "-arg":
                if idx + 1 < len(tokens):
                    extra_flag = tokens[idx + 1]
                    collected_arguments.extend(shlex.split(extra_flag))
                    idx += 2
                else:
                    idx += 1
            else:
                idx += 1

    return collected_arguments


def find_repl_executable() -> list[str] | None:
    """Detect available Rocq or Coq REPL executable command.

    Returns:
        Command token list, or None if no valid REPL is found in PATH.
    """
    candidates = [
        ["rocq", "repl"],
        ["rocq", "top"],
        ["coqtop"],
    ]
    for cmd in candidates:
        try:
            res = subprocess.run(
                cmd + ["-v"],
                capture_output=True,
                text=True,
                timeout=5,
                check=False,
            )
            if res.returncode == 0:
                return cmd
        except (FileNotFoundError, subprocess.TimeoutExpired):
            continue
    return None


def execute_print_assumptions(
    repl_command: list[str],
    module_path: str,
    theorem_name: str,
    project_arguments: list[str],
    working_directory: str,
    timeout_seconds: float,
) -> tuple[int, str, str]:
    """Execute 'Print Assumptions' inside an isolated REPL subprocess.

    Args:
        repl_command: Base REPL command tokens.
        module_path: Logical module path containing the theorem.
        theorem_name: Identifier of the target theorem or lemma.
        project_arguments: Compiler arguments parsed from project file.
        working_directory: Execution directory.
        timeout_seconds: Subprocess timeout in seconds.

    Returns:
        Tuple of (returncode, stdout_text, stderr_text).
    """
    full_command = list(repl_command) + ["-q", "-color", "no"] + project_arguments
    input_script = (
        f"Require Import {module_path}.\nPrint Assumptions {theorem_name}.\nQuit.\n"
    )

    try:
        proc = subprocess.Popen(
            full_command,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=working_directory,
        )
        stdout_text, stderr_text = proc.communicate(
            input=input_script, timeout=timeout_seconds
        )
        return proc.returncode, stdout_text, stderr_text
    except subprocess.TimeoutExpired:
        proc.kill()
        out, err = proc.communicate()
        return 124, out, err + "\nError: Print Assumptions execution timed out."
    except OSError as err:
        return 1, "", f"Subprocess execution error: {err}."


def parse_context_summary(output_text: str) -> dict[str, Any]:
    """Parse Print Assumptions output (CONTEXT SUMMARY or legacy Axioms block).

    Args:
        output_text: Standard output and standard error text from the REPL.

    Returns:
        Structured kernel soundness information dictionary.
    """
    axioms: list[str] = []
    type_in_type_items: list[str] = []
    unsafe_fixpoints: list[str] = []
    nonpositive_inductives: list[str] = []
    unchecked_eliminations: list[str] = []
    indices_not_mattering: list[str] = []

    # Pattern 1: Fully closed proof (no axioms or assumptions)
    if "Closed under the global context" in output_text:
        return {
            "has_context_summary": True,
            "axioms": [],
            "type_in_type": [],
            "unsafe_fixpoints": [],
            "nonpositive_inductives": [],
            "unchecked_eliminations": [],
            "indices_not_mattering": [],
            "raw_output": output_text.strip(),
        }

    has_summary_block = "CONTEXT SUMMARY" in output_text
    lines = output_text.splitlines()
    current_section: str | None = None
    in_legacy_axioms = False

    for line in lines:
        stripped = line.strip()

        # Rocq 9.0+ CONTEXT SUMMARY headers
        if stripped.startswith("* Axioms:"):
            if stripped.endswith("<none>"):
                current_section = None
            else:
                current_section = "axioms"
            continue
        elif stripped.startswith("* Constants/Inductives relying on type-in-type:"):
            if stripped.endswith("<none>"):
                current_section = None
            else:
                current_section = "type_in_type"
            continue
        elif stripped.startswith(
            "* Constants/Inductives relying on unsafe (co)fixpoints:"
        ):
            if stripped.endswith("<none>"):
                current_section = None
            else:
                current_section = "unsafe_fixpoints"
            continue
        elif stripped.startswith("* Inductives whose positivity is assumed:"):
            if stripped.endswith("<none>"):
                current_section = None
            else:
                current_section = "nonpositive"
            continue
        elif stripped.startswith("* Inductives relying on indices not mattering:"):
            if stripped.endswith("<none>"):
                current_section = None
            else:
                current_section = "indices_not_mattering"
            continue
        elif stripped.startswith(
            "* Constants/Inductives relying on unchecked sort eliminations:"
        ):
            current_section = "unchecked_eliminations"
            if not stripped.endswith("<none>"):
                val = stripped.split(":", 1)[1].strip()
                if val:
                    unchecked_eliminations.append(val)
            continue
        elif stripped.startswith("* Theory:"):
            current_section = None
            continue

        # Coq 8.20 Legacy "Axioms:" block detection
        if stripped == "Axioms:" or stripped.startswith("Axioms:"):
            in_legacy_axioms = True
            rem = stripped[len("Axioms:") :].strip()
            if rem and ":" in rem:
                header_match = re.match(
                    r"^([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*:",
                    rem,
                )
                if header_match:
                    axioms.append(header_match.group(1))
            continue

        if current_section and stripped:
            if stripped.startswith("*"):
                current_section = None
                continue
            if not line.startswith((" ", "\t")):
                header_match = re.match(
                    r"^([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*:",
                    stripped,
                )
                if header_match:
                    item = header_match.group(1)
                    if current_section == "axioms":
                        axioms.append(item)
                    elif current_section == "type_in_type":
                        type_in_type_items.append(item)
                    elif current_section == "unsafe_fixpoints":
                        unsafe_fixpoints.append(item)
                    elif current_section == "nonpositive":
                        nonpositive_inductives.append(item)
                    elif current_section == "indices_not_mattering":
                        indices_not_mattering.append(item)
                    elif current_section == "unchecked_eliminations":
                        unchecked_eliminations.append(item)
        elif in_legacy_axioms and stripped:
            if stripped.startswith(("Error:", "Anomaly:", "Rocq <")):
                in_legacy_axioms = False
            elif not line.startswith((" ", "\t")):
                header_match = re.match(
                    r"^([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*:",
                    stripped,
                )
                if header_match:
                    axioms.append(header_match.group(1))

    recognized = has_summary_block or in_legacy_axioms or len(axioms) > 0
    return {
        "has_context_summary": recognized,
        "axioms": axioms,
        "type_in_type": type_in_type_items,
        "unsafe_fixpoints": unsafe_fixpoints,
        "nonpositive_inductives": nonpositive_inductives,
        "unchecked_eliminations": unchecked_eliminations,
        "indices_not_mattering": indices_not_mattering,
        "raw_output": output_text.strip(),
    }


def parse_arguments() -> argparse.Namespace:
    """Parse command-line arguments.

    Returns:
        Parsed arguments namespace.
    """
    parser = argparse.ArgumentParser(
        description="Axiom soundness and kernel assumption auditor for Rocq and Coq theorems.",
    )
    parser.add_argument(
        "--module",
        required=True,
        help="Logical module path containing the theorem (e.g., LF.Basics or MyProject.Core).",
    )
    parser.add_argument(
        "--theorem",
        required=True,
        help="Identifier of the target theorem or lemma (e.g., mult_S_1).",
    )
    parser.add_argument(
        "--project-dir",
        default=".",
        help="Project root directory containing _RocqProject or _CoqProject (default: .).",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=30.0,
        help="Subprocess timeout in seconds (default: 30.0).",
    )
    parser.add_argument(
        "--allow-standard-axioms",
        action="store_true",
        help="Allow approved standard axioms (e.g. functional extensionality, proof irrelevance, excluded middle).",
    )
    parser.add_argument(
        "--allow-tlc-axioms",
        action="store_true",
        help="Allow TLC axiom set for Separation Logic Foundations (SLF).",
    )
    parser.add_argument(
        "--allow-aeneas-axioms",
        action="store_true",
        help="Allow approved Aeneas primitive axioms (slice bounds and architecture scalars).",
    )
    return parser.parse_args()


def main() -> None:
    """Main CLI entrypoint."""
    args = parse_arguments()

    repl_cmd = find_repl_executable()
    if not repl_cmd:
        error_result = {
            "sound": False,
            "module": args.module,
            "theorem": args.theorem,
            "error": "No rocq or coqtop executable found in PATH.",
        }
        print(json.dumps(error_result, indent=2, ensure_ascii=False))
        sys.exit(1)

    project_args = load_project_arguments(args.project_dir)

    returncode, stdout_text, stderr_text = execute_print_assumptions(
        repl_command=repl_cmd,
        module_path=args.module,
        theorem_name=args.theorem,
        project_arguments=project_args,
        working_directory=args.project_dir,
        timeout_seconds=args.timeout,
    )

    combined_output = f"{stdout_text}\n{stderr_text}"
    summary = parse_context_summary(combined_output)

    # Build set of permitted axioms
    allowed_set: set[str] = set()
    if args.allow_standard_axioms:
        allowed_set.update(STANDARD_APPROVED_AXIOMS)
    if args.allow_tlc_axioms:
        allowed_set.update(TLC_APPROVED_AXIOMS)
    if args.allow_aeneas_axioms:
        allowed_set.update(AENEAS_APPROVED_AXIOMS)


    unapproved_axioms: list[str] = []
    admitted_detected = False

    target_clean = args.theorem.strip()
    for ax in summary["axioms"]:
        # If target theorem itself appears as an axiom, consider it unfinished / Admitted
        if target_clean in ax or ax.endswith(f".{target_clean}") or "Admitted" in ax:
            admitted_detected = True
            unapproved_axioms.append(f"{ax} (PROOF UNFINISHED / Admitted)")
            continue

        # Whitelist matching check
        is_allowed = False
        for allowed in allowed_set:
            if ax == allowed or ax.endswith(f".{allowed}"):
                is_allowed = True
                break
        if not is_allowed:
            unapproved_axioms.append(ax)

    has_safety_violations = (
        len(summary["type_in_type"]) > 0
        or len(summary["unsafe_fixpoints"]) > 0
        or len(summary["nonpositive_inductives"]) > 0
        or len(summary["unchecked_eliminations"]) > 0
    )

    is_sound = (
        returncode == 0
        and summary["has_context_summary"]
        and len(unapproved_axioms) == 0
        and not admitted_detected
        and not has_safety_violations
    )

    rejection_reason: str | None = None
    if admitted_detected:
        rejection_reason = "Theorem was Admitted or left unfinished with admit."
    elif len(unapproved_axioms) > 0:
        rejection_reason = f"Disallowed axioms detected: {unapproved_axioms}."
    elif has_safety_violations:
        rejection_reason = "Kernel safety checks violated (e.g. type-in-type or guard condition disabled)."
    elif returncode != 0:
        rejection_reason = f"REPL subprocess failed with returncode {returncode}."

    audit_result = {
        "sound": is_sound,
        "module": args.module,
        "theorem": args.theorem,
        "all_axioms": summary["axioms"],
        "unapproved_axioms": unapproved_axioms,
        "admitted_detected": admitted_detected,
        "type_in_type": summary["type_in_type"],
        "unsafe_fixpoints": summary["unsafe_fixpoints"],
        "nonpositive_inductives": summary["nonpositive_inductives"],
        "unchecked_eliminations": summary["unchecked_eliminations"],
        "indices_not_mattering": summary["indices_not_mattering"],
        "returncode": returncode,
        "rejection_reason": rejection_reason,
        "error": stderr_text.strip() if returncode != 0 else None,
    }

    print(json.dumps(audit_result, indent=2, ensure_ascii=False))
    if not is_sound:
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
