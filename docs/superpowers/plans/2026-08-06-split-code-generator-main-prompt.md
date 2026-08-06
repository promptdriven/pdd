# Splitting the `code_generator_main` Prompt — Phase A: Prompts and Config

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Author nine new prompts under `pdd/prompts/conformance/`, shrink `code_generator_main_python.prompt` to orchestration only, and register everything in `.pddrc` and `architecture.json`.

**Architecture:** Prompts and configuration only. **No code is generated and no tests are written in this plan.** The repo stays fully working throughout because no `.py` file changes — `pdd/code_generator_main.py` remains byte-identical to `main` and every existing import keeps resolving. Verification is therefore static: JSON validity, selector resolution, interface consistency, no dangling symbol references.

**Tech Stack:** PDD prompt format (`/core` style), `architecture.json`, `.pddrc`, Python 3.12 for validation scripts.

**Spec:** `docs/superpowers/specs/2026-08-06-code-generator-main-shared-layer-design.md`

## Explicitly out of scope (Phase B)

Deferred by decision, not oversight:

- Running `pdd generate` / `pdd sync` to produce `pdd/conformance/*.py`.
- `pdd/conformance/__init__.py` — it is a hand-written code file; it belongs with code generation.
- Regenerating `pdd/code_generator_main.py` from the shrunken prompt.
- Test work, including the churn-nonce seam (below).
- Repointing consumers. **Not needed at all** — the orchestrator prompt instructs re-exporting the moved symbols via the redundant-alias form, so all 28 external imports keep resolving from `pdd.code_generator_main`. Dissolving the two lazy-import workarounds is a separate, optional cleanup.

**Carry-forward note for Phase B (the one silent failure).** When `_CHURN_NONCE_CACHE` / `_CHURN_NONCE_READ` / `_read_churn_nonce` move to `pdd/conformance/errors.py`, `tests/test_code_generator_main.py` — which resets them by direct module-attribute assignment on `pdd.code_generator_main`, not via `patch()` — will keep passing while testing nothing. Regenerate that test with `pdd test` in Phase B. This is the only seam here that fails quietly rather than loudly.

## Global Constraints

- **Baseline is `main` @ `c443f2f91`.** Every line span refers to `pdd/code_generator_main.py` at that commit (5,879 lines, 109 top-level symbols). Do not re-derive from another commit.
- **No `.py` file is created or modified by this plan.** If a task makes you want to edit code, stop — it belongs in Phase B.
- **Prompt style — `/core` form:** `%` section markers, **no YAML front-matter**, `<pdd-reason>` and `<pdd-interface>` at top, `<include>context/python_preamble.prompt</include>`, closing `% Deliverables\n  - Code: pdd/conformance/<name>.py`. Target length 22–95 lines, matching `/core`.
- **These four message prefixes are a cross-process contract** parsed by `agentic_sync_runner` from child stdout and must be specified verbatim in the prompts that own them: `Public surface regression for `, `Test churn threshold exceeded for `, `Generation output extraction failure for `, `Architecture conformance error for `.
- **Dependency direction:** `code_generator_main` → `pdd.conformance` → `pdd.interface_semantics`. No conformance prompt may declare a dependency on `code_generator_main_python.prompt`.
- **Python:** `/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python`.
- **Commit after every task.**

### The per-prompt loop (Tasks 2–10)

```bash
# 1. read the source-of-truth code (read-only, for authoring the requirements)
sed -n '<spans>p' pdd/code_generator_main.py | less

# 2. read the source prompt text being moved
sed -n '<prompt lines>p' pdd/prompts/code_generator_main_python.prompt

# 3. author pdd/prompts/conformance/${MOD}_python.prompt
# 4. add the architecture.json entry

# 5. validate (static - no generation)
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python scripts/validate_conformance_prompts.py

# 6. commit
```

---

### Task 1: Config scaffolding and the validation script

Creates the prompts directory, the `.pddrc` context, and a reusable static validator that every later task runs. No `.py` under `pdd/` is touched — the validator lives in `scripts/`.

**Files:**
- Create: `pdd/prompts/conformance/.gitkeep`
- Create: `scripts/validate_conformance_prompts.py`
- Modify: `.pddrc`

**Interfaces:**
- Consumes: nothing.
- Produces: `.pddrc` context `conformance`; `scripts/validate_conformance_prompts.py` exiting non-zero on any inconsistency.

- [ ] **Step 1: Create the prompts directory**

```bash
mkdir -p pdd/prompts/conformance scripts
touch pdd/prompts/conformance/.gitkeep
```

- [ ] **Step 2: Add the `.pddrc` context block**

Insert immediately **before** the `pdd_frontend:` block in `.pddrc`. Order matters — `pdd_cli`'s `paths: ["pdd/**", ...]` would otherwise match first and route output to `pdd/<name>.py`.

```yaml
  conformance:
    paths: ["pdd/conformance/**", "**/pdd/conformance/**", "prompts/conformance/**"]
    defaults:
      generate_output_path: "pdd/conformance/"
      test_output_path: "tests/conformance/"
      example_output_path: "context/conformance/"
      prompts_dir: "prompts/conformance"
      default_language: "python"
      target_coverage: 90.0
      strength: 0.818
      temperature: 0.0
      budget: 10.0
      max_attempts: 3
```

- [ ] **Step 3: Write the validation script**

```python
#!/usr/bin/env python
"""Static validation for the conformance prompt split (Phase A).

Checks prompts and architecture.json only. Generates nothing.
"""
import json
import re
import sys
from pathlib import Path

PROMPT_DIR = Path("pdd/prompts/conformance")
ORCH = Path("pdd/prompts/code_generator_main_python.prompt")
ARCH = Path("architecture.json")

EXPECTED = [
    "errors", "directives", "test_churn", "surface", "signatures",
    "dataclass_signatures", "declared_surface", "annotation_reconcile",
    "interface_check",
]

errors: list[str] = []


def check_prompt(name: str) -> None:
    p = PROMPT_DIR / f"{name}_python.prompt"
    if not p.is_file():
        errors.append(f"{p}: missing")
        return
    text = p.read_text()
    if text.lstrip().startswith("---"):
        errors.append(f"{p}: has YAML front-matter; /core style uses none")
    for tag in ("<pdd-reason>", "<pdd-interface>"):
        if tag not in text:
            errors.append(f"{p}: missing {tag}")
    m = re.search(r"<pdd-interface>\s*(\{.*?\})\s*</pdd-interface>", text, re.S)
    if not m:
        errors.append(f"{p}: <pdd-interface> block not parseable")
    else:
        try:
            iface = json.loads(m.group(1))
        except json.JSONDecodeError as exc:
            errors.append(f"{p}: <pdd-interface> is not valid JSON: {exc}")
        else:
            if iface.get("type") != "module":
                errors.append(f"{p}: interface type must be 'module'")
    if "context/python_preamble.prompt" not in text:
        errors.append(f"{p}: missing the python_preamble include")
    if f"pdd/conformance/{name}.py" not in text:
        errors.append(f"{p}: Deliverables must name pdd/conformance/{name}.py")
    if "code_generator_main" in text:
        errors.append(f"{p}: must not reference code_generator_main (circular)")


def check_architecture() -> None:
    try:
        entries = json.loads(ARCH.read_text())
    except json.JSONDecodeError as exc:
        errors.append(f"{ARCH}: invalid JSON: {exc}")
        return
    by_name = {e.get("filename"): e for e in entries}
    for name in EXPECTED:
        fn = f"conformance/{name}_python.prompt"
        e = by_name.get(fn)
        if e is None:
            errors.append(f"architecture.json: missing entry {fn}")
            continue
        want = f"pdd/conformance/{name}.py"
        if e.get("filepath") != want:
            errors.append(f"architecture.json[{fn}]: filepath is {e.get('filepath')}, want {want}")
        if "interface" not in e:
            errors.append(f"architecture.json[{fn}]: missing interface")
        for dep in e.get("dependencies", []):
            if dep.startswith("conformance/") and dep not in by_name:
                errors.append(f"architecture.json[{fn}]: dependency {dep} not registered")
            if "code_generator_main" in dep:
                errors.append(f"architecture.json[{fn}]: must not depend on code_generator_main")


def check_orchestrator_selector() -> None:
    """The line-168 selector must only name symbols still in the module."""
    if not ORCH.is_file():
        errors.append(f"{ORCH}: missing")
        return
    text = ORCH.read_text()
    src = Path("pdd/code_generator_main.py").read_text()
    for m in re.finditer(r'select="([^"]*)"', text):
        for sym in m.group(1).split(","):
            sym = sym.strip()
            if not sym.startswith(("def:", "class:")):
                continue
            kind, _, nm = sym.partition(":")
            pat = rf"^{'class' if kind == 'class' else 'def'} {re.escape(nm)}\b"
            if not re.search(pat, src, re.M) and not re.search(
                rf"^\s+def {re.escape(nm)}\b", src, re.M
            ):
                errors.append(f"{ORCH}: selector names missing symbol {sym}")


def main() -> int:
    for name in EXPECTED:
        check_prompt(name)
    check_architecture()
    check_orchestrator_selector()
    if errors:
        print("FAIL")
        for e in errors:
            print("  -", e)
        return 1
    print(f"OK - {len(EXPECTED)} prompts, architecture.json consistent, selector resolves")
    return 0


if __name__ == "__main__":
    sys.exit(main())
```

- [ ] **Step 4: Run it — expect failure, nine prompts missing**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python scripts/validate_conformance_prompts.py
```

Expected: `FAIL` listing nine missing prompts and nine missing architecture entries. This is the failing test for Tasks 2–10.

- [ ] **Step 5: Verify `.pddrc` path resolution**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.config_resolution import resolve_effective_config
cfg = resolve_effective_config(prompt_file='pdd/prompts/conformance/errors_python.prompt')
print('generate_output_path:', cfg.get('generate_output_path'))
assert str(cfg.get('generate_output_path')).rstrip('/').endswith('conformance'), cfg
print('OK')
"
```

If it resolves to `pdd` rather than `pdd/conformance/`, the block is below `pdd_cli:` — move it up.

- [ ] **Step 6: Confirm no code changed**

```bash
git status --porcelain -- 'pdd/**/*.py' | grep -v '^$' && echo "VIOLATION - code changed" || echo "OK - no .py under pdd/ touched"
```

- [ ] **Step 7: Commit**

```bash
git add .pddrc scripts/validate_conformance_prompts.py pdd/prompts/conformance/.gitkeep
git commit -m "chore(conformance): add .pddrc context and static prompt validator"
```

---

### Task 2: `errors_python.prompt`

First because every other prompt references these exception types. **The only prompt that must be composed from interleaved fragments rather than lifted whole** — the exception contracts are scattered across prompt sections 5, 5a, 5b and 5c, next to the gate logic that raises them.

**Files:**
- Create: `pdd/prompts/conformance/errors_python.prompt`
- Modify: `architecture.json`

**Interfaces:**
- Consumes: nothing.
- Produces (declared in `<pdd-interface>`): `ArchitectureConformanceError`, `PublicSurfaceRegressionError`, `TestChurnError`, `ProseOutputError`. Later prompts reference these by name.

- [ ] **Step 1: Read the ground truth (read-only)**

```bash
sed -n '71,89p;92,163p;166,289p;292,332p;335,435p' pdd/code_generator_main.py > /tmp/errors.reference.py
wc -l /tmp/errors.reference.py    # ~352
```

- [ ] **Step 2: Read the prompt fragments to move**

```bash
sed -n '66,91p'   pdd/prompts/code_generator_main_python.prompt   # §5  ArchitectureConformanceError contract
sed -n '92p'      pdd/prompts/code_generator_main_python.prompt   # §5a ProseOutputError contract (complete)
sed -n '93,131p'  pdd/prompts/code_generator_main_python.prompt   # §5b PublicSurfaceRegressionError contract
sed -n '132,143p' pdd/prompts/code_generator_main_python.prompt   # §5c TestChurnError contract + nonce
sed -n '204,214p' pdd/prompts/code_generator_main_python.prompt   # Deliverables 5,7,8
```

Take only the **exception contracts** — attributes, constructor order, message format, `repair_directive` text. Leave the gate *algorithms* for Tasks 4–10.

- [ ] **Step 3: Author the prompt**

```
<pdd-reason>Typed exceptions raised by the PDD conformance gates, shared by sync_main, sync_orchestration, one_session_sync, cmd_test_main and agentic_test_generate.</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "ArchitectureConformanceError", "signature": "(prompt_name: str, output_path: str, architecture_entry: Dict[str, Any], expected_symbols: List[str], found_symbols: List[str], missing_symbols: List[str], message: Optional[str] = None, total_cost: float = 0.0, model_name: str = \"unknown\", repair_directive: Optional[str] = None)", "returns": "ArchitectureConformanceError"},
      {"name": "PublicSurfaceRegressionError", "signature": "(prompt_name: str, output_path: str, removed_symbols: List[str], pre_surface_size: int, post_surface_size: int, changed_signatures: Optional[List[str]] = None, total_cost: float = 0.0, model_name: str = \"unknown\", repair_directive: Optional[str] = None, signature_details: Optional[List[Tuple[str, str, str, str]]] = None)", "returns": "PublicSurfaceRegressionError"},
      {"name": "TestChurnError", "signature": "(prompt_name: str, output_path: str, churn_ratio: float, threshold: float, pre_line_count: int, post_line_count: int, total_cost: float = 0.0, model_name: str = \"unknown\", repair_directive: Optional[str] = None, adopted_human: bool = False)", "returns": "TestChurnError"},
      {"name": "ProseOutputError", "signature": "(prompt_name: str, output_path: str, language: str, model_name: str = \"unknown\", total_cost: float = 0.0, raw_output: Optional[str] = None, extractor_result: str = \"empty\")", "returns": "ProseOutputError"}
    ]
  }
}
</pdd-interface>

# prompts/conformance/errors_python.prompt
% You are an expert Python engineer. Your goal is to write the typed conformance
% exceptions for the PDD CLI in `pdd/conformance/errors.py`.

% Role & Scope
  Defines the four `click.UsageError` subclasses raised by the PDD conformance
  gates, plus the churn-nonce provenance helper and the shared test-file
  extension tuple. Contains NO gate logic - only the exception types, their
  structured attributes, diagnostic message formats, and repair directives.

<include>context/python_preamble.prompt</include>

% Requirements
  [Paste the exception contracts gathered in Step 2. For EACH class specify:
   constructor parameter order verbatim, every structured attribute with its
   type, the exact message prefix and field lines, and the repair_directive text.]

  N. **Peer hierarchy**: all four subclass `click.UsageError`. NONE is a subclass
     of another - `ProseOutputError` is explicitly a peer of
     `ArchitectureConformanceError`, not a subclass.

  N. **Churn nonce**: `_read_churn_nonce()` reads the FD named by the
     `PDD_CHURN_NONCE_FD` env var exactly ONCE, caching via module globals
     `_CHURN_NONCE_CACHE` and `_CHURN_NONCE_READ`. Accepts only a plausible hex
     token. Returns `""` when no channel is present. Grandchild test subprocesses
     do not inherit the FD under default `close_fds`, so untrusted test code
     cannot learn the nonce even though it can read the env var. `TestChurnError`
     appends a `nonce: <token>` line only when a token is available.

  N. **Module-level constants**: `_LANGUAGE_TEST_FILE_EXTS` (tuple seeded with
     `.py`, `.go`, `.rb`, `.rs`, `.exs`, `.ex`, `.dart`, `.clj`, `.cljc`, `.lua`,
     `.php`) and `PROSE_OUTPUT_REPAIR_DIRECTIVE`.

% Message-format contract - CROSS-PROCESS, DO NOT CHANGE
  These prefixes are string-matched by `agentic_sync_runner` on child-process
  stdout and MUST be byte-identical:
  - `Architecture conformance error for {prompt_name}:`
  - `Public surface regression for {prompt_name}:`
  - `Test churn threshold exceeded for {prompt_name}:`
  - `Generation output extraction failure for {prompt_name}:`
  `PublicSurfaceRegressionError` additionally lists `removed:`,
  `signature_changed:`, `output:`, `pre_surface_size:`, `post_surface_size:` on
  their own lines, then appends one compact one-line
  `signature_detail: <json.dumps({...})>` per `signature_details` tuple AFTER
  those fields, which stay byte-identical.

% Dependencies
  - Imports `click`, `json`, `os`, `re`.
  - Imports `Any`, `Dict`, `List`, `Optional`, `Tuple` from `typing`.

% Instructions
  - This module is imported by every other conformance module. It must import
    none of them, and must never import `pdd.code_generator_main`.

% Deliverables
  - Code: `pdd/conformance/errors.py`
```

- [ ] **Step 4: Add the `architecture.json` entry**

Append, modelled on the existing `core/errors_python.prompt` entry:

```json
{
  "reason": "Typed exceptions raised by the PDD conformance gates.",
  "description": "Defines ArchitectureConformanceError, PublicSurfaceRegressionError, TestChurnError and ProseOutputError as peer click.UsageError subclasses, plus the churn-nonce provenance helper and the shared test-file extension tuple. Message prefixes are a cross-process contract parsed by agentic_sync_runner from child stdout.",
  "dependencies": [],
  "priority": 5,
  "filename": "conformance/errors_python.prompt",
  "filepath": "pdd/conformance/errors.py",
  "tags": ["conformance", "python", "errors"],
  "interface": {"type": "module", "module": {"functions": ["... copy the four entries from the <pdd-interface> block in Step 3 ..."]}}
}
```

- [ ] **Step 5: Validate**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python scripts/validate_conformance_prompts.py
```

Expected: eight prompts still missing, but **no error mentioning `errors_python.prompt`**.

- [ ] **Step 6: Confirm the interface block matches architecture.json**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
import json, re
t = open('pdd/prompts/conformance/errors_python.prompt').read()
iface = json.loads(re.search(r'<pdd-interface>\s*(\{.*?\})\s*</pdd-interface>', t, re.S).group(1))
arch = {e['filename']: e for e in json.load(open('architecture.json'))}['conformance/errors_python.prompt']
a = [f['name'] for f in iface['module']['functions']]
b = [f['name'] for f in arch['interface']['module']['functions']]
assert a == b, (a, b)
assert a == ['ArchitectureConformanceError','PublicSurfaceRegressionError','TestChurnError','ProseOutputError'], a
print('OK - prompt and architecture.json agree')
"
```

- [ ] **Step 7: Commit**

```bash
git add pdd/prompts/conformance/errors_python.prompt architecture.json
git commit -m "feat(conformance): add errors_python.prompt for the four typed gate exceptions"
```

---

### Task 3: `directives_python.prompt`

**Files:** Create `pdd/prompts/conformance/directives_python.prompt`; modify `architecture.json`.

**Interfaces:**
- Consumes: nothing.
- Produces: `_prompt_breaking_change_removed_symbols`, `_prompt_breaking_change_signature_symbols`, `_prompt_allows_breaking_change`, `_env_flag_enabled`, `_strip_yaml_front_matter`.

- [ ] **Step 1: Read ground truth** — `sed -n '439,454p;467,506p;513,516p;525,626p;2403,2405p' pdd/code_generator_main.py > /tmp/directives.reference.py`
- [ ] **Step 2: Source prompt text** — the `BREAKING-CHANGE` grammar bullets inside §5b, prompt lines 93–131.
- [ ] **Step 3: Author the prompt.** `/core` style. Requirements that MUST survive:
  - Directives are **anchored**: `^\s*BREAKING-CHANGE:\s*` with `re.MULTILINE`. Buried mid-line mentions (`See the BREAKING-CHANGE: marker doc`) must NOT register.
  - Removal verbs `remove`/`delete`/`drop`/`rename` (+ `-s`/`-d`/`-ing`); signature verbs `change`/`changes`/`changed`/`changing` followed by `signature`/`signatures`/`api`/`contract`.
  - Symbol grammar: comma-separated identifiers, bare or wrapped in **matching** backticks / single / double quotes. Mismatched wrappers rejected. Tokens with embedded whitespace rejected, so `BREAKING-CHANGE: remove old_helper to opt out` whitelists only `old_helper`.
  - A bare `BREAKING-CHANGE:` marker must NOT disable any gate globally.
  - **Descendant expansion**: a top-level class name in a removal allow-list implicitly authorizes removing every captured `Class.method` / `Class.Inner.method` descendant. Removal verbs ONLY — signature-change directives stay strict per-symbol.
  - `_env_flag_enabled` / `_parse_llm_bool` for `PDD_*` flag parsing.
- [ ] **Step 4: Add the `architecture.json` entry** — `filename: conformance/directives_python.prompt`, `filepath: pdd/conformance/directives.py`, `dependencies: []`, `priority: 5`, `tags: ["conformance","python","directives"]`.
- [ ] **Step 5: Validate** — `python scripts/validate_conformance_prompts.py`; no error mentioning `directives_python.prompt`.
- [ ] **Step 6: Commit** — `git commit -m "feat(conformance): add directives_python.prompt for BREAKING-CHANGE parsing"`

---

### Task 4: `test_churn_python.prompt`

**Files:** Create `pdd/prompts/conformance/test_churn_python.prompt`; modify `architecture.json`.

**Interfaces:**
- Consumes: `errors.TestChurnError`, `directives._env_flag_enabled`.
- Produces: `_verify_test_churn`, `_compute_test_churn_ratio`, `_get_test_churn_threshold`, `_is_test_output_path`, `_prompt_allows_test_churn`, `_find_default_test_files`.

- [ ] **Step 1: Read ground truth** — `sed -n '633,654p;657,769p;3184,3238p;3241,3277p;4315,4335p' pdd/code_generator_main.py > /tmp/test_churn.reference.py`
- [ ] **Step 2: Source prompt text** — §5c, prompt lines 132–143 (6,559 chars). Lift nearly whole.
- [ ] **Step 3: Author the prompt.** Requirements that MUST survive:
  - Test-path taxonomy: `tests/`, `__tests__/`, singular `__test__/` (#1903); `test_` prefix; the lowercase `_test.<ext>`/`_spec.<ext>` family over `_LANGUAGE_TEST_FILE_EXTS`; the **case-sensitive** PascalCase JVM/.NET/Swift family (so `latest.kt` / `manifest.java` do not false-positive); the **case-insensitive** JS/TS `.test.`/`.spec.` family including `.mjs`/`.cjs`.
  - Opt-out grammar: an anchored directive pairing an opt-out verb with `tests` **as the verb's direct object**. `BREAKING-CHANGE: drop foo and rewrite tests` opts out; `BREAKING-CHANGE: rewrite docs and update tests` does not.
  - `_compute_test_churn_ratio`: stdlib `difflib.unified_diff`; count `+`/`-` excluding `+++`/`---`; return `0.0` if nothing removed; else `max(added, removed) / max(len(pre_lines), 1)` capped at `1.0`; empty pre → `0.0`.
  - Threshold: `PDD_TEST_CHURN_THRESHOLD` default `0.40`, accepting `"0.40"` or `"40%"`; unparseable logs a warning and falls back to `0.40`; clamp `[0.0, 1.0]`.
  - `adopted_human` forwarded through `_verify_test_churn` (default `False`).
  - `PDD_SKIP_TEST_CHURN_GATE=1` disables only this gate; `PDD_SKIP_CONFORMANCE=1` disables all.
- [ ] **Step 4: `architecture.json` entry** — `dependencies: ["conformance/errors_python.prompt", "conformance/directives_python.prompt"]`.
- [ ] **Step 5: Validate.**
- [ ] **Step 6: Commit** — `git commit -m "feat(conformance): add test_churn_python.prompt for the test-churn gate"`

---

### Task 5: `surface_python.prompt`

**Files:** Create `pdd/prompts/conformance/surface_python.prompt`; modify `architecture.json`.

**Interfaces:**
- Consumes: nothing (stdlib `ast`; `pdd.split_validation.collect_patch_symbols_for_module`).
- Produces: `_snapshot_public_surface`, `_diff_public_surface`, `_extract_dunder_all`, `_collect_patch_targets`, `_reexport_binding`, `_collect_bound_module_names`, `_symbol_exists_in_module`.

- [ ] **Step 1: Read ground truth** — `sed -n '772,822p;826,840p;843,1131p;1134,1311p;2398,2400p' pdd/code_generator_main.py > /tmp/surface.reference.py`
- [ ] **Step 2: Source prompt text** — the `_snapshot_public_surface` bullets of §5b.
- [ ] **Step 3: Author the prompt.** Requirements that MUST survive:
  - **`__all__` precedence**: authoritative when a clean `ast.Assign` / bound `ast.AnnAssign` of a `List`/`Tuple` of string `Constant`s. A name is public **iff** in `__all__`, even underscore-prefixed; names not in `__all__` are not public. Filter to names actually bound at module scope.
  - **Source order, last write wins.** A bare `__all__: T` annotation is a no-op; **any other write RESETS to unresolvable**. So `__all__ = [...]; __all__.append(...); __all__ = [...]` is resolvable again.
  - `_subtree_mutates_dunder_all` descends into `if`/`for`/`while`/`with`/`try`/`match` but NOT into def/class/lambda scopes or their headers, and does not flag comprehension loop targets. It reports: computed values, non-string elements, `AugAssign`, mutator methods (**not** read-only `.copy()`/`.index()`), subscript/slice store or delete, any other store/delete of the bare name, walrus, `for`/`with` targets, pattern/exception captures binding via a STRING field, and imports that BIND `__all__`.
  - Classes in `__all__` contribute **recursively-walked members at every depth**, regardless of underscore prefix.
  - **Fallback heuristic**: top-level `FunctionDef`/`AsyncFunctionDef`/`ClassDef`; dotted names for methods and nested classes at every depth; skip dunders; skip single-underscore names at any depth unless patch targets; module-level `Assign`/bound `AnnAssign` with bare-`Name` targets including Tuple/List/Starred unpacking, capturing `AnnAssign` **only** when `node.value is not None`.
  - **Imports are surface ONLY as explicit re-exports.** `_reexport_binding(alias)` returns the bound name when `alias.asname is not None and alias.asname == alias.name and not alias.asname.startswith("_")`. Plain imports are implementation detail (#1662/#1663/pdd_cloud#2256). Skip `from X import *`. **Skip `from __future__ import …` entirely**, in both this helper and `_collect_bound_module_names`.
  - Non-Python languages return `set()`.
- [ ] **Step 4: `architecture.json` entry** — `dependencies: []`.
- [ ] **Step 5: Validate.**
- [ ] **Step 6: Commit** — `git commit -m "feat(conformance): add surface_python.prompt for __all__ resolution and surface snapshot"`

---

### Task 6: `dataclass_signatures_python.prompt`

Before `signatures` because `_snapshot_public_signatures` calls into it.

**Files:** Create `pdd/prompts/conformance/dataclass_signatures_python.prompt`; modify `architecture.json`.

**Interfaces:**
- Consumes: nothing (stdlib `ast`).
- Produces: `_synthesize_dataclass_init_signature`, `_collect_dataclass_own_parts`, `_collect_dataclass_inherited_parts`, `_is_dataclass_decorator`, `_dataclass_decorator_is_kw_only`, `_dataclass_decorator_synthesizes_init`, `_is_kw_only_sentinel`, `_dataclass_field_call_is_init_false`, `_part_field_name`.

- [ ] **Step 1: Read ground truth** — `sed -n '1459,1930p' pdd/code_generator_main.py > /tmp/dataclass_signatures.reference.py`
- [ ] **Step 2: Source prompt text** — the `@dataclass` bullet of §5b.
- [ ] **Step 3: Author the prompt.** Requirements that MUST survive:
  - Synthesise from class-body `ast.AnnAssign` fields in **source order** when there is no explicit `__init__`; an explicit `__init__` always wins.
  - `@dataclass(kw_only=True)` — both bare `dataclass` and `dataclasses.dataclass` forms — emits a single leading `*`.
  - In-body `_: KW_ONLY` sentinel (`KW_ONLY` Name or `dataclasses.KW_ONLY` Attribute) recognised **before** the underscore-prefix skip; fields before stay positional, after become kw-only.
  - Decorator **and** sentinel together emit only ONE `*` (decorator wins). A trailing `*` with no kw-only fields after it is stripped so `(*)` never appears.
  - `InitVar[...]` included (constructor params, though not stored); `ClassVar[...]` excluded per PEP 557; `field(init=False, ...)` / `dataclasses.field(init=False, ...)` excluded, but `init=True`, a missing `init` kwarg, or any non-`field` call keeps the field.
  - Inherited fields in **REVERSE-MRO order** — `class C(A, B)` synthesises `(b, a, c)`. A base decorated `@dataclass(init=False)` STILL contributes its fields. Cross-module bases emit a single `[inherited_unresolved]` token. A derived redeclaration wins on annotation/default text but keeps the **base's original position**.
- [ ] **Step 4: `architecture.json` entry** — `dependencies: []`.
- [ ] **Step 5: Validate.**
- [ ] **Step 6: Commit** — `git commit -m "feat(conformance): add dataclass_signatures_python.prompt for constructor synthesis"`

---

### Task 7: `signatures_python.prompt`

**Files:** Create `pdd/prompts/conformance/signatures_python.prompt`; modify `architecture.json`.

**Interfaces:**
- Consumes: `surface` (`_extract_dunder_all`, `_collect_bound_module_names`, `_reexport_binding`, `_effective_patch_targets`), `dataclass_signatures._synthesize_dataclass_init_signature`.
- Produces: `_snapshot_public_signatures`, `_format_python_signature`, `_python_method_binding_kind`, `_python_property_accessor_role`, `_class_constructor_signature`, `_resolve_class_node`, `_patch_target_signature_entry`.

- [ ] **Step 1: Read ground truth** — `sed -n '1314,1456p;1933,2032p;2035,2395p' pdd/code_generator_main.py > /tmp/signatures.reference.py`
- [ ] **Step 2: Source prompt text** — the `_snapshot_public_signatures` bullets of §5b.
- [ ] **Step 3: Author the prompt.** Requirements that MUST survive:
  - **The same** `__all__` precedence, class-member recursion, patch-target preservation, explicit-re-export rule and `from __future__` skip as `surface`. State this explicitly: the two must agree on what is public, or the removed-symbol diff and the signature diff disagree.
  - Every entry carries a **leading kind prefix**: `[function]` / `[async_function]` / `[class]` at top level; `[instance]` / `[staticmethod]` / `[classmethod]` / `[property:<roles>]` in classes; `[assignment]` for module-level rebindings; `[import]`, `[import:<module>]`, `[import:from <module>]`, `[import:from <module>:<source>]` for re-exports.
  - A **redundant** alias (`asname == name`) canonicalises to the **plain** marker, not the renaming-alias marker — otherwise normalising `from pathlib import Path as Path` → `from pathlib import Path` diffs as a phantom change.
  - For `ImportFrom` the recorded module includes the relative level: `"." * node.level + (node.module or "")`, so `from . import Foo as Foo` → `from .. import Foo as Foo` diffs as `[import:from .]` vs `[import:from ..]` rather than colliding on an empty string.
  - Import entries reach the dict ONLY when public — a clean `__all__` lists the bound name, OR `_reexport_binding(alias)` is non-`None`.
- [ ] **Step 4: `architecture.json` entry** — `dependencies: ["conformance/surface_python.prompt", "conformance/dataclass_signatures_python.prompt"]`.
- [ ] **Step 5: Validate.**
- [ ] **Step 6: Commit** — `git commit -m "feat(conformance): add signatures_python.prompt for signature snapshotting"`

---

### Task 8: `declared_surface_python.prompt`

**Files:** Create `pdd/prompts/conformance/declared_surface_python.prompt`; modify `architecture.json`.

**Interfaces:**
- Consumes: `errors` (`PublicSurfaceRegressionError`, `ArchitectureConformanceError`), `surface`, `signatures`, `directives`, `pdd.interface_semantics` (`signature_entries_compatible`, `build_module_default_symbols`).
- Produces: `_verify_public_surface_regression`, `_collect_declared_surface`, `_declared_signature_to_entry`, `_entry_binding_context`, `_declared_presence_name`, `_declared_patch_targets`.

- [ ] **Step 1: Read ground truth** — `sed -n '2408,2915p' pdd/code_generator_main.py > /tmp/declared_surface.reference.py`
- [ ] **Step 2: Source prompt text** — the #1900 / #1012 / #1612 / #1558 bullets of §5b.
- [ ] **Step 3: Author the prompt.** Requirements that MUST survive:
  - **Syntax pre-check (#1612)**: when a pre-generation surface exists, `ast.parse(generated_code)` FIRST. A `SyntaxError` raises `ArchitectureConformanceError` — **not** `PublicSurfaceRegressionError` — with a syntax-focused repair directive, so a truncated generation is not mis-diagnosed as "all symbols removed".
  - **Prompt-declared interface as contract (#1900)**: `type: "module"` only; `cli`/`command` names excluded. Declared top-level functions compared against the DECLARED signature with **both** `old_symbols` and `new_symbols` from `build_module_default_symbols(generated_code)`. Declared dotted methods and `Class.__init__` are receiver-stripped. Only symbols with a parseable paren signature join `declared_validated`; only those are excluded from the old-code baseline.
  - **Semantic comparison (#1558)**: `signature_entries_compatible`, not string equality; per-side default-symbol tables from each module version; do NOT short-circuit on equal text for callables; fall back to exact-string equality only when it returns `None`.
  - `BREAKING-CHANGE: change signature <sym>` on a DECLARED symbol relaxes only the un-declarable binding-kind/async, never the declared params.
  - Repair directive built from `pdd-interface` details must inject the declared signature as a **VERBATIM** hard constraint — reproduce the declared annotation text token-for-token, never substitute an equivalent spelling (`object` stays `object`, never `Any`), never broaden with union members the declaration omits (#1968).
  - First-time generation exempt. `PDD_SKIP_PUBLIC_SURFACE_GATE=1` disables only this gate.
- [ ] **Step 4: `architecture.json` entry** — `dependencies: ["conformance/errors_python.prompt", "conformance/surface_python.prompt", "conformance/signatures_python.prompt", "conformance/directives_python.prompt"]`.
- [ ] **Step 5: Validate.**
- [ ] **Step 6: Commit** — `git commit -m "feat(conformance): add declared_surface_python.prompt for the public-surface gate"`

---

### Task 9: `annotation_reconcile_python.prompt`

**Files:** Create `pdd/prompts/conformance/annotation_reconcile_python.prompt`; modify `architecture.json`.

**Interfaces:**
- Consumes: `declared_surface._collect_declared_surface`, `pdd.interface_semantics.annotations_compatible`.
- Produces: `_reconcile_declared_annotation_drift`, `_annotation_only_edits`, `_apply_byte_edits`, `_node_byte_span`, `_line_start_byte_offsets`, `_signature_slots`, `_parse_declared_def`, `_index_function_defs`.

- [ ] **Step 1: Read ground truth** — `sed -n '2918,3181p' pdd/code_generator_main.py > /tmp/annotation_reconcile.reference.py`
- [ ] **Step 2: Source prompt text** — the #1968 bullet of §5b.
- [ ] **Step 3: Author the prompt.** Requirements that MUST survive:
  - Runs immediately BEFORE the public-surface gate; when it returns a non-`None` string, that is what the gate checks and the writer persists.
  - Rewrites only when a declared `type: "module"` symbol's generated signature differs from the declaration **ONLY** in annotation spelling — identical parameter names, order, kinds and defaults, and only annotations `annotations_compatible` deems INCOMPATIBLE.
  - The rewrite is a **UTF-8 byte-offset splice** on the emitted annotation node.
  - **Fail-safe**: any structural drift disqualifies that symbol (left to the gate); a compatible alias (`Dict` vs `dict`) is never churned; the whole rewrite is discarded if the reconciled source no longer parses.
  - Returns `None` unless at least one annotation was reconciled — it must never alter an otherwise-passing generation. `PDD_SKIP_ANNOTATION_RECONCILE=1` bypasses it.
- [ ] **Step 4: `architecture.json` entry** — `dependencies: ["conformance/declared_surface_python.prompt"]`.
- [ ] **Step 5: Validate.**
- [ ] **Step 6: Commit** — `git commit -m "feat(conformance): add annotation_reconcile_python.prompt for #1968 convergence"`

---

### Task 10: `interface_check_python.prompt`

**Files:** Create `pdd/prompts/conformance/interface_check_python.prompt`; modify `architecture.json`.

**Interfaces:**
- Consumes: `errors.ArchitectureConformanceError`, `pdd.interface_semantics` (`annotations_compatible`, `compare_default_sources`, `build_module_default_symbols`).
- Produces: `_verify_architecture_conformance`, `_verify_architecture_json_conformance`, `_verify_pdd_interface_signatures`, `_extract_pdd_interface_signatures`, `_collect_pdd_interface_names`, `_find_target_function`, `_collect_python_symbols`, `ParamSpec`, `_ast_args_to_specs`, `_parse_declared_param_names`, `_collect_actual_param_names`, `_parse_declared_param_specs`, `_collect_actual_param_specs`.

- [ ] **Step 1: Read ground truth** — `sed -n '3485,3573p;3581,3635p;3638,4247p' pdd/code_generator_main.py > /tmp/interface_check.reference.py`
- [ ] **Step 2: Source prompt text** — §5 (prompt lines 66–91, 10,445 chars) plus the Architecture-Logic paragraph of `% Instructions` (prompt line ~197).
- [ ] **Step 3: Author the prompt.** Requirements that MUST survive:
  - Three inspected `<pdd-interface>` shapes: `type: "module"` (`module.functions`), `type: "cli"` (`cli.commands`), `type: "command"` (`command.commands`, or a single `command` dict with `name`/`signature`). Entries omitting `signature` are silent no-ops.
  - Dotted declarations (`ContentSelector.select`) resolved by descending nested `ClassDef` nodes by name, then matching the final segment as a `def`/`async def`.
  - Three checks in priority order: **missing function/method** → bare names in `missing_funcs`; **missing parameter** → dotted `func.param` in `missing_params`, with `**kwargs`/`*args` NOT satisfying a declared named parameter; **signature drift** → annotation drift only when BOTH sides annotate and they are not `annotations_compatible`; default drift raised when the declared default is dropped (`<no default>` sentinel) or `compare_default_sources` returns `INCOMPATIBLE` **or** `UNKNOWN` (fail closed), suppressed only on `COMPATIBLE`.
  - Each category in its **own sentence** so the subprocess parser routes correctly: `declares function(s)/method(s) missing from the generated code: ...`, `declares parameter(s) missing from the generated code: ...`, `declares parameter(s) whose signature drifted in the generated code: <func.param> (<kind>: declared \`<src>\`, found \`<src>\`), ...`.
  - `repair_directive` groups dotted method params with **`rpartition('.')`, not `partition('.')`** — `ContentSelector.select.mode` attributes to function `ContentSelector.select` with parameter `mode`, not class `ContentSelector` with parameter `select.mode`. It must NOT instruct removing the declared parameter from the prompt.
  - camelCase guard exempts names declared in EITHER `architecture.json` `module.functions` OR the prompt's own `<pdd-interface>`, collected by `_collect_pdd_interface_names` — which includes description-only declarations and therefore must NOT reuse the signature-gated `_extract_pdd_interface_signatures` (#1446).
  - Do NOT descend into `if`/`try`/`with` inside class bodies — conformance is a hard validator and must not accept branch-conditional methods.
  - Missing `<pdd-interface>` → skip silently; malformed JSON → `logger.warning` and skip, never raise.
- [ ] **Step 4: `architecture.json` entry** — `dependencies: ["conformance/errors_python.prompt"]`.
- [ ] **Step 5: Validate** — all nine prompts now present; the script's prompt and architecture checks should pass.
- [ ] **Step 6: Commit** — `git commit -m "feat(conformance): add interface_check_python.prompt for architecture and pdd-interface conformance"`

---

### Task 11: Shrink the orchestrator prompt

Hazards H1, H2 and H3 all land here. Do not split this task — the prompt body, its `<pdd-interface>`, its selector and the `architecture.json` entry must change together.

**Files:**
- Modify: `pdd/prompts/code_generator_main_python.prompt`
- Modify: `architecture.json` (the `code_generator_main_python.prompt` entry)

**Interfaces:**
- Consumes: all nine conformance prompts.
- Produces: an orchestrator prompt at roughly 29% of its former size.

- [ ] **Step 1: Trim the line-168 selector from 36 symbols to 11 (H1)**

Keep exactly: `def:code_generator_main`, `def:_run_discovery`, `def:_should_wire_generated_exports`, `def:_wire_to_parent_init`, `def:_parse_front_matter`, `def:_expand_vars`, `def:_run_git_command`, `def:is_git_repository`, `def:get_git_content_at_ref`, `def:get_file_git_status`, `def:git_add_files`.

Remove these 25: `pattern:^ParamSpec\s*=`, `class:ArchitectureConformanceError`, `class:PublicSurfaceRegressionError`, `class:TestChurnError`, `class:ProseOutputError`, `def:_verify_architecture_conformance`, `def:_verify_architecture_json_conformance`, `def:_verify_pdd_interface_signatures`, `def:_extract_pdd_interface_signatures`, `def:_collect_declared_surface`, `def:_declared_signature_to_entry`, `def:_declared_presence_name`, `def:_declared_patch_targets`, `def:_entry_binding_context`, `def:_class_constructor_signature`, `def:_resolve_class_node`, `def:_symbol_exists_in_module`, `def:_patch_target_signature_entry`, `def:_parse_declared_param_names`, `def:_collect_actual_param_names`, `def:_parse_declared_param_specs`, `def:_collect_actual_param_specs`, `def:_ast_args_to_specs`, `def:_find_target_function`, `def:_collect_python_symbols`.

- [ ] **Step 2: Verify the selector**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
import re
line = open('pdd/prompts/code_generator_main_python.prompt').read().split('\n')[167]
syms = [s.strip() for s in re.search(r'select=\"([^\"]*)\"', line).group(1).split(',')]
assert len(syms) == 11, (len(syms), syms)
assert not any('Error' in s for s in syms), syms
print('OK - 11 symbols remain')
"
```

- [ ] **Step 3: Remove the four exception entries from `<pdd-interface>` (H2)**

Leave exactly `is_git_repository`, `get_git_content_at_ref`, `get_file_git_status`, `git_add_files`, `code_generator_main`.

- [ ] **Step 4: Remove prompt sections 5, 5a, 5b, 5c** (lines 66–143) and the Deliverables items describing the moved helpers and exception classes. Keep sections 1, 2, 3, 4, 6 and the orchestration parts of `% Instructions`.

- [ ] **Step 5: Add `<pdd-dependency>` lines** for all nine conformance prompts, alongside the existing eleven.

- [ ] **Step 6: Add the re-export requirement (H3)**

This is what keeps all 28 external imports resolving, so no consumer has to change:

```
- **Re-export the conformance gate surface.** Import the gate entry points from
  `pdd.conformance` and re-export the four typed exceptions using the REDUNDANT
  ALIAS form, so they register as explicit re-exports rather than removals:
      from .conformance.errors import ArchitectureConformanceError as ArchitectureConformanceError
      from .conformance.errors import ProseOutputError as ProseOutputError
      from .conformance.errors import PublicSurfaceRegressionError as PublicSurfaceRegressionError
      from .conformance.errors import TestChurnError as TestChurnError
  A plain `from ... import X` is NOT public surface under this module's own
  public-surface rules and would be read as symbol removal. Also re-export the
  gate helpers that external callers import today, so
  `from pdd.code_generator_main import ...` keeps resolving for every one of
  them.
```

- [ ] **Step 7: Add the one-time BREAKING-CHANGE line** to the prompt body — the `[class]` → `[import:from …]` binding-kind flip is a signature change the gate is specified to diff:

```
BREAKING-CHANGE: change signature ArchitectureConformanceError, PublicSurfaceRegressionError, TestChurnError, ProseOutputError
```

- [ ] **Step 8: Update the `architecture.json` orchestrator entry** — remove the four exception entries from `interface.module.functions`; append the nine `conformance/*_python.prompt` names to `dependencies`.

- [ ] **Step 9: Verify architecture.json consistency**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
import json
d = json.load(open('architecture.json'))
by = {e['filename']: e for e in d}
cg = by['code_generator_main_python.prompt']
names = [f['name'] for f in cg['interface']['module']['functions']]
assert names == ['is_git_repository','get_git_content_at_ref','get_file_git_status','git_add_files','code_generator_main'], names
conf = sorted(k for k in by if k.startswith('conformance/'))
assert len(conf) == 9, conf
for c in conf:
    assert c in cg['dependencies'], f'orchestrator missing dep {c}'
print('OK -', len(d), 'entries;', len(conf), 'conformance; orchestrator interface trimmed')
"
```

- [ ] **Step 10: Confirm the prompt shrank**

```bash
wc -c pdd/prompts/code_generator_main_python.prompt
```

Expected roughly 21,000 chars, down from 71,311 (~29%).

- [ ] **Step 11: Commit**

```bash
git add pdd/prompts/code_generator_main_python.prompt architecture.json
git commit -m "refactor(prompt): move the gate sections out of code_generator_main_python.prompt"
```

---

### Task 12: Phase A verification

**Files:** none modified.

- [ ] **Step 1: Full static validation**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python scripts/validate_conformance_prompts.py
```

Expected: `OK - 9 prompts, architecture.json consistent, selector resolves`.

- [ ] **Step 2: Prove no code changed — the defining property of Phase A**

```bash
git diff --stat main -- 'pdd/**/*.py' 'tests/**/*.py' 'context/**/*.py'
```

Expected: **empty**. Any output means code was touched and belongs in Phase B.

- [ ] **Step 3: The repo still works untouched**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -m pytest -q -p no:randomly \
    tests/test_issue_67.py tests/test_issue_67_expansion.py \
    tests/test_issue_1558_semantic_contracts.py tests/test_issue_1968_annotation_convergence.py \
    tests/test_prompt_contract_validation.py tests/test_issue_1903_adopt_collocated_test.py \
    tests/test_issue_686_post_process_args_braces.py tests/test_cmd_test_main.py 2>&1 | tail -3
```

Must be unchanged from `main` — no `.py` file was modified, so any difference is environmental.

- [ ] **Step 4: Confirm prompt sizes match the `/core` target**

```bash
wc -l pdd/prompts/conformance/*.prompt
```

`/core` prompts run 22–95 lines. A conformance prompt far above that suggests requirement text was copied rather than distilled — acceptable given the density of §5b, but worth a look.

- [ ] **Step 5: Dry-run sync to preview Phase B**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/pdd sync code_generator_main --dry-run --json 2>&1 | tail -20
```

Informational only. It should report the prompt as changed and code regeneration as pending — exactly what Phase B will do. Do **not** act on it here.

- [ ] **Step 6: Commit**

```bash
git commit --allow-empty -m "chore(conformance): phase A complete - 9 prompts, config and architecture registered, no code touched"
```

---

## Phase B (not this plan)

In order, once Phase A is reviewed:

1. Hand-write `pdd/conformance/__init__.py` (10 lines, per `pdd/core/__init__.py`).
2. Generate the nine modules, one at a time, diffing each against the `/tmp/*.reference.py` extractions above.
3. Regenerate `pdd/code_generator_main.py`; verify the re-exports use the redundant-alias form and that its public surface lost nothing.
4. Regenerate `tests/test_code_generator_main.py` with `pdd test` — this is what fixes the silent churn-nonce seam.
5. Optional cleanup: repoint consumers at `pdd.conformance` and drop the two lazy-import workarounds.

## Self-Review Notes

**Spec coverage for Phase A:** `.pddrc` context → Task 1. Nine prompts → Tasks 2–10. Prompt style → Global Constraints + validator. `architecture.json` registration → every module task + Task 11. H1 selector → Task 11 Steps 1–2. H2 interface migration → Task 11 Steps 3, 8, 9. H3 re-export instruction → Task 11 Steps 6–7 (as prompt text; its effect is verified in Phase B). H4 churn nonce → carried forward, explicitly. H5 patch call sites → no action needed; all 27 targets stay in the orchestrator. H6 → pre-existing note only.

**Deliberately deferred:** everything that writes a `.py` file. `context/conformance/*_example.py` and `tests/conformance/` are not created — `/core` covers only 6 of 9 modules with examples and 3 of 9 with tests, so these should follow the modules, not precede them.

**Known weak point:** Task 2's prompt is composed from interleaved fragments rather than lifted whole, and every other prompt depends on the exception names it declares. Get it reviewed before Task 3.
