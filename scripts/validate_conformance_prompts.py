#!/usr/bin/env python
"""Static validation for the conformance prompt split (Phase A).

Checks prompts and architecture.json only. Generates nothing, imports no
project code, and never writes a file. Exits non-zero on any inconsistency.
"""
from __future__ import annotations

import ast
import json
import re
import sys
from pathlib import Path

PROMPT_DIR = Path("pdd/prompts/conformance")
ORCH = Path("pdd/prompts/code_generator_main_python.prompt")
SOURCE = Path("pdd/code_generator_main.py")
ARCH = Path("architecture.json")

EXPECTED = [
    "gate_errors",
    "directives",
    "test_churn",
    "surface",
    "declared_surface",
    "interface_check",
]

# This is the compatibility surface retained in code_generator_main after the
# conformance split.  Keep it explicit: deriving the requirement from the
# source module would let a future regeneration silently shrink the contract.
REQUIRED_CONFORMANCE_REEXPORTS = frozenset({
    "ArchitectureConformanceError", "LanguageMismatchError", "PROSE_OUTPUT_REPAIR_DIRECTIVE", "ProseOutputError", "PublicSurfaceRegressionError", "TestChurnError",
    "_CHURN_NONCE_CACHE", "_CHURN_NONCE_ENV", "_CHURN_NONCE_READ", "_LANGUAGE_TEST_FILE_EXTS", "_read_churn_nonce", "_verify_language_validity",
    "_BREAKING_CHANGE_DIRECTIVE_RE", "_DIRECTIVE_SYMBOL_RE", "_YAML_FRONT_MATTER_RE", "_env_flag_enabled", "_iter_breaking_change_directives", "_parse_breaking_change_symbols",
    "_parse_llm_bool", "_prompt_allows_breaking_change", "_prompt_breaking_change_removed_symbols", "_prompt_breaking_change_signature_symbols", "_prompt_has_breaking_change_marker", "_strip_yaml_front_matter",
    "_COMPREHENSION_TYPES", "_DUNDER_ALL_MUTATOR_METHODS", "_SCOPE_NODE_TYPES", "_assign_target_matches", "_class_constructor_signature", "_clean_dunder_all_literal",
    "_collect_bound_module_names", "_collect_dataclass_inherited_parts", "_collect_dataclass_own_parts", "_collect_patch_targets", "_collect_python_public_surface", "_dataclass_decorator_is_kw_only",
    "_dataclass_decorator_synthesizes_init", "_dataclass_field_call_is_init_false", "_diff_public_surface", "_effective_patch_targets", "_extract_dunder_all", "_format_python_signature",
    "_is_dataclass_decorator", "_is_kw_only_sentinel", "_node_writes_dunder_all", "_part_field_name", "_patch_target_signature_entry", "_python_method_binding_kind",
    "_python_property_accessor_role", "_reexport_binding", "_resolve_class_node", "_scannable_children", "_snapshot_public_signatures", "_snapshot_public_surface",
    "_subtree_mutates_dunder_all", "_symbol_exists_in_module", "_synthesize_dataclass_init_signature", "_TEST_CHURN_BRIDGE_BREAK_RE", "_TEST_CHURN_OPT_OUT_RE", "_TEST_CHURN_TARGET_RE",
    "_calculate_test_churn_ratio", "_compute_test_churn_ratio", "_find_default_test_files", "_get_test_churn_threshold", "_is_python_generation", "_is_test_output_path",
    "_prompt_allows_test_churn", "_verify_test_churn", "ParamSpec", "_ast_args_to_specs", "_collect_actual_param_specs", "_collect_pdd_interface_names",
    "_collect_python_symbols", "_extract_pdd_interface_signatures", "_find_target_function", "_parse_declared_param_specs", "_verify_architecture_conformance", "_verify_architecture_json_conformance",
    "_verify_pdd_interface_signatures", "_annotation_only_edits", "_apply_byte_edits", "_collect_declared_surface", "_declared_patch_targets", "_declared_presence_name",
    "_declared_signature_to_entry", "_entry_binding_context", "_index_function_defs", "_line_start_byte_offsets", "_node_byte_span", "_parse_declared_def",
    "_reconcile_declared_annotation_drift", "_signature_slots", "_verify_public_surface_regression",
})

# Mirrors pdd.contract_ir: a <contract_rules> line is read as a rule ID when it
# matches _EXPLICIT_ID_RE or _SEQ_ID_RE, and as a MALFORMED one when it matches
# only _CANDIDATE_ID_RE. A rule that wraps onto a hyphenated word ("prose-wrapped")
# therefore reads as a broken rule ID, which `pdd contracts check` rejects.
RULE_ID_RE = re.compile(r"^(R-?\d+|RULE-?\d+)\b", re.IGNORECASE)
SEQ_ID_RE = re.compile(r"^(\d+)[.):\s]")
CANDIDATE_ID_RE = re.compile(r"^([A-Z]{1,5}[-_]\w+)\b", re.IGNORECASE)

errors: list[str] = []


def _interface_block(text: str) -> str | None:
    m = re.search(r"<pdd-interface>\s*(\{.*?\})\s*</pdd-interface>", text, re.S)
    return m.group(1) if m else None


# Mirrors pdd.contract_ir._XML_SECTION_RE. That scan is non-greedy but
# non-overlapping, so a bare `<tag>` written in prose pairs with the next real
# `</tag>` and swallows everything between them. A <contract_rules> block inside
# that span is invisible to `pdd contracts check` while still looking correct to
# a line-anchored search, which is a silent loss of coverage evidence.
XML_SECTION_RE = re.compile(
    r"<(?P<tag>[a-z_][a-z0-9_]*)>(?P<body>.*?)</(?P=tag)>",
    re.IGNORECASE | re.DOTALL,
)


def check_rules_are_reachable(path: Path, text: str) -> None:
    """Require <contract_rules> to survive the real parser's section scan."""
    scan = "\n".join(
        line for line in text.splitlines() if not line.lstrip().startswith("%")
    )
    tags = {m.group("tag").lower() for m in XML_SECTION_RE.finditer(scan)}
    if "<contract_rules>" in text and "contract_rules" not in tags:
        errors.append(
            f"{path}: <contract_rules> is present but swallowed by an unpaired "
            "tag written in prose; `pdd contracts check` will not see it"
        )


def check_contract_rules(path: Path, text: str) -> None:
    """Require a parseable <contract_rules> block.

    Without the XML tags `pdd checkup coverage` reports "No <contract_rules>
    section" and `pdd contracts check` passes vacuously, so the rules carry no
    coverage evidence at all.
    """
    block = re.search(r"^<contract_rules>$(.*?)^</contract_rules>$", text, re.S | re.M)
    if block is None:
        errors.append(f"{path}: missing a <contract_rules> block")
        return

    rule_ids: list[str] = []
    for line in block.group(1).splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if RULE_ID_RE.match(stripped) or SEQ_ID_RE.match(stripped):
            rule_ids.append(stripped.split(".")[0].split()[0])
        elif CANDIDATE_ID_RE.match(stripped):
            token = CANDIDATE_ID_RE.match(stripped).group(1)
            errors.append(
                f"{path}: line starting '{token}' parses as a malformed rule ID; "
                "rewrap so no continuation line begins with a hyphenated word"
            )
    if not rule_ids:
        errors.append(f"{path}: <contract_rules> declares no rules")


def check_prompt(name: str) -> None:
    path = PROMPT_DIR / f"{name}_python.prompt"
    if not path.is_file():
        errors.append(f"{path}: missing")
        return
    text = path.read_text(encoding="utf-8")

    if text.lstrip().startswith("---"):
        errors.append(f"{path}: has YAML front-matter; /core style uses none")
    for tag in ("<pdd-reason>", "<pdd-interface>"):
        if tag not in text:
            errors.append(f"{path}: missing {tag}")

    raw = _interface_block(text)
    if raw is None:
        errors.append(f"{path}: <pdd-interface> block not parseable")
    else:
        try:
            iface = json.loads(raw)
        except json.JSONDecodeError as exc:
            errors.append(f"{path}: <pdd-interface> is not valid JSON: {exc}")
        else:
            if iface.get("type") != "module":
                errors.append(f"{path}: interface type must be 'module'")
            elif not iface.get("module", {}).get("functions"):
                errors.append(f"{path}: interface declares no functions")

    if "context/python_preamble.prompt" not in text:
        errors.append(f"{path}: missing the python_preamble include")
    if f"pdd/conformance/{name}.py" not in text:
        errors.append(f"{path}: Deliverables must name pdd/conformance/{name}.py")
    if "code_generator_main" in text:
        errors.append(f"{path}: must not reference code_generator_main (circular)")

    check_contract_rules(path, text)
    check_rules_are_reachable(path, text)
    check_declared_signatures(name)


def check_architecture() -> None:
    if not ARCH.is_file():
        errors.append(f"{ARCH}: missing")
        return
    try:
        entries = json.loads(ARCH.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        errors.append(f"{ARCH}: invalid JSON: {exc}")
        return

    by_name = {e.get("filename"): e for e in entries}
    for name in EXPECTED:
        filename = f"conformance/{name}_python.prompt"
        entry = by_name.get(filename)
        if entry is None:
            errors.append(f"architecture.json: missing entry {filename}")
            continue
        want = f"pdd/conformance/{name}.py"
        if entry.get("filepath") != want:
            errors.append(
                f"architecture.json[{filename}]: filepath is "
                f"{entry.get('filepath')!r}, want {want!r}"
            )
        if "interface" not in entry:
            errors.append(f"architecture.json[{filename}]: missing interface")
        for dep in entry.get("dependencies", []):
            if "code_generator_main" in dep:
                errors.append(
                    f"architecture.json[{filename}]: must not depend on code_generator_main"
                )
            if dep.startswith("conformance/") and dep not in by_name:
                errors.append(
                    f"architecture.json[{filename}]: dependency {dep} not registered"
                )

        prompt_path = PROMPT_DIR / f"{name}_python.prompt"
        if prompt_path.is_file() and "interface" in entry:
            raw = _interface_block(prompt_path.read_text(encoding="utf-8"))
            if raw:
                try:
                    prompt_iface = json.loads(raw)
                except json.JSONDecodeError:
                    prompt_iface = None
                if prompt_iface:
                    a = [f["name"] for f in prompt_iface.get("module", {}).get("functions", [])]
                    b = [
                        f["name"]
                        for f in entry["interface"].get("module", {}).get("functions", [])
                        if isinstance(f, dict)
                    ]
                    if a != b:
                        errors.append(
                            f"architecture.json[{filename}]: interface names {b} "
                            f"disagree with the prompt's {a}"
                        )


def _real_signatures(module_path: Path) -> dict[str, str]:
    """Return {symbol: "(args) -> Ret"} for a module's top-level definitions."""
    tree = ast.parse(module_path.read_text(encoding="utf-8"))
    out: dict[str, str] = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            ret = ast.unparse(node.returns) if node.returns else "None"
            out[node.name] = f"({ast.unparse(node.args)}) -> {ret}"
        elif isinstance(node, ast.ClassDef):
            init = next(
                (b for b in node.body
                 if isinstance(b, ast.FunctionDef) and b.name == "__init__"),
                None,
            )
            if init is not None:
                args = re.sub(r"^self,\s*", "", ast.unparse(init.args))
                out[node.name] = f"({args})"
    return out


def check_declared_signatures(name: str) -> None:
    """Require the prompt's declared signatures to equal the module's real ones.

    A prompt is the source of truth for regeneration, so a drifted declaration is
    not a documentation defect: `pdd sync` would emit a module whose callers break
    at the first call, and `declared_surface` judges declared symbols against the
    declaration, so the wrong shape becomes the enforced one. Presence checks
    (`hasattr`) cannot catch this — only shape comparison can.
    """
    module = Path("pdd/conformance") / f"{name}.py"
    prompt = PROMPT_DIR / f"{name}_python.prompt"
    if not module.is_file() or not prompt.is_file():
        return  # prompt-only phase: nothing generated yet
    raw = _interface_block(prompt.read_text(encoding="utf-8"))
    if raw is None:
        return
    try:
        declared = json.loads(raw)["module"]["functions"]
        real = _real_signatures(module)
    except (json.JSONDecodeError, KeyError, SyntaxError) as exc:
        errors.append(f"{prompt}: cannot compare signatures: {exc}")
        return

    def norm(text: str) -> str:
        return re.sub(r"\s+", "", text or "").replace("'", '"')

    for entry in declared:
        sym = entry.get("name")
        if sym not in real:
            continue  # constants and re-exports carry no callable signature
        if norm(entry.get("signature")) != norm(real[sym]):
            errors.append(
                f"{prompt}: declared signature for {sym} does not match "
                f"{module}\n      declared: {entry.get('signature')}"
                f"\n      actual  : {real[sym]}"
            )


def check_orchestrator_selector() -> None:
    """The include selector must only name symbols still present in the module."""
    if not ORCH.is_file():
        errors.append(f"{ORCH}: missing")
        return
    if not SOURCE.is_file():
        errors.append(f"{SOURCE}: missing")
        return
    text = ORCH.read_text(encoding="utf-8")
    src = SOURCE.read_text(encoding="utf-8")

    # The prompt carries several <include select=...> blocks; only the one whose
    # body is the generated module itself is a self-include whose symbols must
    # still exist there. The others point at context/ example files.
    self_includes = [
        m
        for m in re.finditer(r'<include select="([^"]*)"\s*>([^<]*)</include>', text)
        if m.group(2).strip() == str(SOURCE)
    ]
    if not self_includes:
        errors.append(f"{ORCH}: no self-include selector found for {SOURCE}")
        return

    for match in self_includes:
        for raw in match.group(1).split(","):
            sym = raw.strip()
            if not sym.startswith(("def:", "class:")):
                continue
            kind, _, nm = sym.partition(":")
            keyword = "class" if kind == "class" else "def"
            top = re.search(rf"^{keyword} {re.escape(nm)}\b", src, re.M)
            nested = re.search(rf"^\s+{keyword} {re.escape(nm)}\b", src, re.M)
            if not top and not nested:
                errors.append(f"{ORCH}: selector names missing symbol {sym}")


def check_orchestrator_compatibility_reexports() -> None:
    """Require regenerating context for every conformance compatibility alias."""
    if not ORCH.is_file() or not SOURCE.is_file():
        return
    text = ORCH.read_text(encoding="utf-8")
    try:
        tree = ast.parse(SOURCE.read_text(encoding="utf-8"))
    except SyntaxError as exc:
        errors.append(f"{SOURCE}: cannot parse compatibility aliases: {exc}")
        return

    reexport_nodes = [
        node for node in tree.body
        if isinstance(node, ast.ImportFrom)
        and node.level == 1
        and node.module is not None
        and node.module.startswith("conformance.")
    ]
    actual = {
        alias.asname or alias.name
        for node in reexport_nodes
        for alias in node.names
    }
    missing = REQUIRED_CONFORMANCE_REEXPORTS - actual
    unexpected = actual - REQUIRED_CONFORMANCE_REEXPORTS
    if missing or unexpected:
        details = []
        if missing:
            details.append("missing " + ", ".join(sorted(missing)))
        if unexpected:
            details.append("unexpected " + ", ".join(sorted(unexpected)))
        errors.append(f"{SOURCE}: conformance compatibility aliases drifted: " + "; ".join(details))

    ranges = []
    for match in re.finditer(r"<include\b(?P<attrs>[^>]*)>(?P<path>[^<]*)</include>", text):
        if match.group("path").strip() != str(SOURCE):
            continue
        lines = re.search(r'\blines="(\d+)-(\d+)"', match.group("attrs"))
        if lines:
            ranges.append((int(lines.group(1)), int(lines.group(2))))
    if not ranges:
        errors.append(f"{ORCH}: missing line-range include for conformance compatibility exports")
        return

    uncovered = [
        node for node in reexport_nodes
        if not any(start <= node.lineno <= node.end_lineno <= end for start, end in ranges)
    ]
    if uncovered:
        errors.append(
            f"{ORCH}: compatibility include omits "
            + ", ".join(f".{node.module}" for node in uncovered)
        )


def check_orchestrator_contract_rules() -> None:
    """The orchestrator carries the gate obligations the units cannot own.

    Atomicity on a failing gate and the prose/empty classification live here, not
    in any conformance unit, so without a parseable block the story's central
    criterion - a failing check never alters the file on disk - would carry no
    coverage evidence and `pdd contracts check` would pass vacuously on it.
    """
    if not ORCH.is_file():
        errors.append(f"{ORCH}: missing")
        return
    text = ORCH.read_text(encoding="utf-8")
    check_contract_rules(ORCH, text)
    check_rules_are_reachable(ORCH, text)


def main() -> int:
    for name in EXPECTED:
        check_prompt(name)
    check_architecture()
    check_orchestrator_selector()
    check_orchestrator_compatibility_reexports()
    check_orchestrator_contract_rules()

    if errors:
        print("FAIL")
        for err in errors:
            print("  -", err)
        return 1
    print(
        f"OK - {len(EXPECTED)} prompts, architecture.json consistent, selector resolves"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
