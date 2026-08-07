#!/usr/bin/env python
"""Static validation for the conformance prompt split (Phase A).

Checks prompts and architecture.json only. Generates nothing, imports no
project code, and never writes a file. Exits non-zero on any inconsistency.
"""
from __future__ import annotations

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


def main() -> int:
    for name in EXPECTED:
        check_prompt(name)
    check_architecture()
    check_orchestrator_selector()

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
