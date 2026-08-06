# Splitting the `code_generator_main` Prompt — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Split `pdd/prompts/code_generator_main_python.prompt` (71,311 chars, 70.8% of which is conformance-gate text) into nine focused prompts under `pdd/prompts/conformance/`, and regenerate the code from them so behavior is unchanged.

**Architecture:** Additive first, switchover second. Phase 1 creates nine new prompts and generates nine new modules while `code_generator_main.py` stays untouched — the suite must stay green throughout because nothing yet depends on the new code. Phase 2 flips the orchestrator over to importing them, shrinks its prompt, and repoints consumers. This gives a safe checkpoint between "new code exists" and "old code removed."

**Tech Stack:** PDD CLI (`pdd sync`, `pdd generate`), Python 3.12, pytest, Click, `architecture.json`, `.pddrc`.

**Spec:** `docs/superpowers/specs/2026-08-06-code-generator-main-shared-layer-design.md`

## Global Constraints

- **Baseline is `main` @ `c443f2f91`.** Every line span in this plan refers to `pdd/code_generator_main.py` at that commit (5,879 lines, 109 top-level symbols). Do not re-derive spans from a different commit.
- **Prompts are the source of truth.** Never hand-edit a generated `.py` under `pdd/conformance/`. If a module will not converge, fix its prompt and regenerate.
- **Behavior preservation is the acceptance criterion.** No functional change, no signature change, no message-format change.
- **These four string prefixes are a cross-process contract** parsed by `agentic_sync_runner` from child stdout and must stay byte-identical: `Public surface regression for `, `Test churn threshold exceeded for `, `Generation output extraction failure for `, `Architecture conformance error for `.
- **Python env:** all commands run under the `pdd` conda env. Absolute interpreter: `/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python`. CLI: `/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/pdd`.
- **Prompt style:** `/core` form — `%` section markers, **no YAML front-matter**, `<pdd-reason>` and `<pdd-interface>` at top, `<include>context/python_preamble.prompt</include>`, closing `% Deliverables\n  - Code: pdd/conformance/<name>.py`.
- **Dependency direction:** `code_generator_main` → `pdd.conformance` → `pdd.interface_semantics`. `pdd.conformance` must never import `code_generator_main`.
- **Commit after every task.** Never batch.

### The per-module loop (Tasks 2–10)

Every module task follows this exact loop. `$MOD` is the module name, `$SPANS` its line spans.

```bash
# 1. extract the source text for reference (read-only)
sed -n '<span>p' pdd/code_generator_main.py > /tmp/$MOD.reference.py

# 2. author pdd/prompts/conformance/${MOD}_python.prompt   (see task for content)
# 3. add the architecture.json entry                        (see task for content)

# 4. generate
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/pdd --strength .9 --temperature 0 \
    generate --output pdd/conformance/$MOD.py \
    pdd/prompts/conformance/${MOD}_python.prompt

# 5. DRIFT CHECK - the primary detector. Compare generated vs reference.
diff -u /tmp/$MOD.reference.py pdd/conformance/$MOD.py | head -100

# 6. import check
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c \
    "import pdd.conformance.$MOD as m; print(sorted(n for n in dir(m) if not n.startswith('__')))"

# 7. suite must still be green (nothing imports the new module yet)
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -m pytest -q -p no:randomly \
    tests/test_issue_67.py tests/test_issue_67_expansion.py \
    tests/test_issue_1558_semantic_contracts.py tests/test_issue_1968_annotation_convergence.py \
    tests/test_prompt_contract_validation.py tests/test_issue_1903_adopt_collocated_test.py \
    tests/test_issue_686_post_process_args_braces.py tests/test_cmd_test_main.py

# 8. commit
```

**Step 5 is the gate.** The generated module must be semantically equivalent to the reference — same function bodies, same regexes, same constants, same message strings. Cosmetic differences (import order, docstring wording, blank lines) are acceptable. Any behavioral difference means the prompt is under-specified: fix the prompt and regenerate. Do not accept a module you have not diffed.

---

### Task 1: Scaffolding and path resolution

Creates the directory structure, the `.pddrc` context, and the hand-written `__init__.py`. Proves `pdd` resolves conformance paths correctly *before* any prompt is written — if this is wrong, all nine modules generate to the wrong location.

**Files:**
- Create: `pdd/conformance/__init__.py`
- Create: `pdd/prompts/conformance/.gitkeep`, `context/conformance/.gitkeep`, `tests/conformance/__init__.py`
- Modify: `.pddrc` (add a `conformance:` context block)

**Interfaces:**
- Consumes: nothing.
- Produces: the `pdd.conformance` package; `.pddrc` context `conformance` mapping `prompts/conformance` → `pdd/conformance/`.

- [ ] **Step 1: Create directories**

```bash
mkdir -p pdd/conformance pdd/prompts/conformance context/conformance tests/conformance
touch pdd/prompts/conformance/.gitkeep context/conformance/.gitkeep
touch tests/conformance/__init__.py
```

- [ ] **Step 2: Add the `.pddrc` context block**

Insert immediately **before** the `pdd_frontend:` block in `.pddrc` (order matters — `pdd_cli`'s `paths: ["pdd/**", ...]` would otherwise match first and write to `pdd/<name>.py`):

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

- [ ] **Step 3: Write the hand-written `__init__.py`**

Modelled on `pdd/core/__init__.py`. The four exception classes do not exist yet, so this file is written now but only becomes importable after Task 2. Write it with the import commented out, and uncomment in Task 2.

```python
"""Conformance gates for PDD code generation.

Extracted from ``code_generator_main`` so that ``sync_orchestration``,
``one_session_sync``, ``cmd_test_main`` and ``agentic_test_generate`` can
consume the gate layer without importing the generation pipeline.
"""

# Enabled in Task 2, once pdd/conformance/errors.py exists.
# from .errors import (
#     ArchitectureConformanceError,
#     ProseOutputError,
#     PublicSurfaceRegressionError,
#     TestChurnError,
# )

__all__ = [
    'ArchitectureConformanceError',
    'ProseOutputError',
    'PublicSurfaceRegressionError',
    'TestChurnError',
]
```

- [ ] **Step 4: Verify path resolution**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.config_resolution import resolve_effective_config
cfg = resolve_effective_config(prompt_file='pdd/prompts/conformance/errors_python.prompt')
print('generate_output_path:', cfg.get('generate_output_path'))
print('prompts_dir:', cfg.get('prompts_dir'))
"
```

Expected: `generate_output_path: pdd/conformance/`. If it prints `pdd` or `pdd/`, the `conformance:` block is in the wrong position — move it above `pdd_cli:`.

- [ ] **Step 5: Record the baseline test result**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -m pytest -q -p no:randomly \
    tests/test_issue_67.py tests/test_issue_67_expansion.py \
    tests/test_issue_1558_semantic_contracts.py tests/test_issue_1968_annotation_convergence.py \
    tests/test_prompt_contract_validation.py tests/test_issue_1903_adopt_collocated_test.py \
    tests/test_issue_686_post_process_args_braces.py tests/test_cmd_test_main.py 2>&1 | tail -3
```

Write the pass/skip counts into the commit message. Every later task compares against these numbers.

- [ ] **Step 6: Commit**

```bash
git add pdd/conformance pdd/prompts/conformance context/conformance tests/conformance .pddrc
git commit -m "chore(conformance): scaffold package, prompts dir, and .pddrc context"
```

---

### Task 2: `errors.py` — the four typed exceptions

First because every other module raises these. **This is the only prompt that must be composed from fragments rather than lifted whole** — the exception contracts are interleaved with the gate logic that raises them, across prompt sections 5, 5a, 5b and 5c.

**Files:**
- Create: `pdd/prompts/conformance/errors_python.prompt`
- Create: `pdd/conformance/errors.py` (generated, 352 lines)
- Modify: `architecture.json`, `pdd/conformance/__init__.py`

**Interfaces:**
- Consumes: nothing.
- Produces: `ArchitectureConformanceError(prompt_name, output_path, architecture_entry, expected_symbols, found_symbols, missing_symbols, message=None, total_cost=0.0, model_name="unknown", repair_directive=None)`; `PublicSurfaceRegressionError(prompt_name, output_path, removed_symbols, pre_surface_size, post_surface_size, changed_signatures=None, total_cost=0.0, model_name="unknown", repair_directive=None, signature_details=None)`; `TestChurnError(prompt_name, output_path, churn_ratio, threshold, pre_line_count, post_line_count, total_cost=0.0, model_name="unknown", repair_directive=None, adopted_human=False)`; `ProseOutputError(prompt_name, output_path, language, model_name="unknown", total_cost=0.0, raw_output=None, extractor_result="empty")`; plus `_read_churn_nonce() -> str`, `PROSE_OUTPUT_REPAIR_DIRECTIVE`, `_LANGUAGE_TEST_FILE_EXTS`, `_CHURN_NONCE_ENV`, `_CHURN_NONCE_CACHE`, `_CHURN_NONCE_READ`.

- [ ] **Step 1: Extract the reference**

```bash
{ sed -n '71,89p'  pdd/code_generator_main.py
  sed -n '92,163p' pdd/code_generator_main.py
  sed -n '166,289p' pdd/code_generator_main.py
  sed -n '292,332p' pdd/code_generator_main.py
  sed -n '335,435p' pdd/code_generator_main.py; } > /tmp/errors.reference.py
wc -l /tmp/errors.reference.py   # expect ~352
```

- [ ] **Step 2: Gather the prompt source fragments**

The exception contracts live in these places in `pdd/prompts/code_generator_main_python.prompt`:

```bash
sed -n '66,91p'   pdd/prompts/code_generator_main_python.prompt  # §5  - ArchitectureConformanceError contract
sed -n '92p'      pdd/prompts/code_generator_main_python.prompt  # §5a - ProseOutputError contract (full)
sed -n '93,131p'  pdd/prompts/code_generator_main_python.prompt  # §5b - PublicSurfaceRegressionError contract
sed -n '132,143p' pdd/prompts/code_generator_main_python.prompt  # §5c - TestChurnError contract + nonce
sed -n '204,214p' pdd/prompts/code_generator_main_python.prompt  # Deliverables 5,7,8 - class contracts
```

Pull only the **exception attribute/message/repair_directive contracts** from these; leave the gate *algorithms* behind for Tasks 4–10.

- [ ] **Step 3: Write the prompt**

Create `pdd/prompts/conformance/errors_python.prompt`:

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
  This module defines the four `click.UsageError` subclasses raised by the PDD
  conformance gates, plus the churn-nonce provenance helper. It contains NO gate
  logic - only the exception types, their structured attributes, their diagnostic
  message formats, and their repair directives.

<include>context/python_preamble.prompt</include>

% Requirements
  [PASTE the exception contracts gathered in Step 2 here, verbatim where possible.
   Each class MUST specify: constructor parameter order, every structured
   attribute, the exact message prefix, and the repair_directive text.]

% Message-format contract (CROSS-PROCESS - DO NOT CHANGE)
  These prefixes are string-matched by `agentic_sync_runner` on child-process
  stdout and MUST be byte-identical:
  - `Architecture conformance error for {prompt_name}:`
  - `Public surface regression for {prompt_name}:`
  - `Test churn threshold exceeded for {prompt_name}:`
  - `Generation output extraction failure for {prompt_name}:`

% Dependencies
  - Imports `click`, `json`, `os`, `re`.
  - Imports `Any`, `Dict`, `List`, `Optional`, `Tuple` from `typing`.
  - MUST NOT import `pdd.code_generator_main` (circular).

% Instructions
  - `ArchitectureConformanceError`, `PublicSurfaceRegressionError`,
    `TestChurnError` and `ProseOutputError` are PEERS. None is a subclass of
    another; all subclass `click.UsageError`.
  - `_read_churn_nonce()` reads the FD named by `PDD_CHURN_NONCE_FD` exactly once,
    caches via `_CHURN_NONCE_CACHE` / `_CHURN_NONCE_READ`, accepts only a
    plausible hex token, and returns `""` when no channel is present.

% Deliverables
  - Code: `pdd/conformance/errors.py`
```

- [ ] **Step 4: Add the `architecture.json` entry**

Append an entry modelled on the existing `core/errors_python.prompt` entry:

```json
{
  "reason": "Typed exceptions raised by the PDD conformance gates.",
  "description": "Defines ArchitectureConformanceError, PublicSurfaceRegressionError, TestChurnError and ProseOutputError as peer click.UsageError subclasses, plus the churn-nonce provenance helper. Message prefixes are a cross-process contract parsed by agentic_sync_runner.",
  "dependencies": [],
  "priority": 5,
  "filename": "conformance/errors_python.prompt",
  "filepath": "pdd/conformance/errors.py",
  "tags": ["conformance", "python", "errors"],
  "interface": { "...": "copy the <pdd-interface> module block from Step 3" }
}
```

- [ ] **Step 5: Generate**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/pdd --strength .9 --temperature 0 \
    generate --output pdd/conformance/errors.py \
    pdd/prompts/conformance/errors_python.prompt
```

- [ ] **Step 6: Drift check — the gate**

```bash
diff -u /tmp/errors.reference.py pdd/conformance/errors.py | head -120
```

Verify by inspection: all four message prefixes byte-identical; every constructor parameter present in the same order; `repair_directive` text unchanged. Reject and re-prompt on any behavioral difference.

- [ ] **Step 7: Enable the `__init__.py` re-export**

Uncomment the `from .errors import (...)` block written in Task 1 Step 3.

- [ ] **Step 8: Verify import and message formats**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance import ArchitectureConformanceError, PublicSurfaceRegressionError, TestChurnError, ProseOutputError
import click
for c in (ArchitectureConformanceError, PublicSurfaceRegressionError, TestChurnError, ProseOutputError):
    assert issubclass(c, click.UsageError), c
    assert not any(issubclass(c, o) for o in (ArchitectureConformanceError, PublicSurfaceRegressionError, TestChurnError, ProseOutputError) if o is not c), f'{c} must be a peer'
e = TestChurnError('p.prompt', 'out.py', 0.9, 0.4, 100, 10)
assert str(e).startswith('Test churn threshold exceeded for p.prompt:'), str(e)[:80]
print('OK - four peer exceptions, prefixes intact')
"
```

- [ ] **Step 9: Run the suite (must match Task 1 baseline)**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -m pytest -q -p no:randomly \
    tests/test_issue_67.py tests/test_issue_67_expansion.py \
    tests/test_issue_1558_semantic_contracts.py tests/test_issue_1968_annotation_convergence.py \
    tests/test_prompt_contract_validation.py tests/test_issue_1903_adopt_collocated_test.py \
    tests/test_issue_686_post_process_args_braces.py tests/test_cmd_test_main.py 2>&1 | tail -3
```

- [ ] **Step 10: Commit**

```bash
git add pdd/prompts/conformance/errors_python.prompt pdd/conformance/errors.py \
        pdd/conformance/__init__.py architecture.json
git commit -m "feat(conformance): extract typed gate exceptions into pdd/conformance/errors.py"
```

---

### Task 3: `directives.py` — `BREAKING-CHANGE` parsing and env flags

**Files:**
- Create: `pdd/prompts/conformance/directives_python.prompt`, `pdd/conformance/directives.py` (152 lines)
- Modify: `architecture.json`

**Interfaces:**
- Consumes: nothing.
- Produces: `_parse_llm_bool(value: str) -> bool`, `_env_flag_enabled(name: str) -> bool`, `_strip_yaml_front_matter(prompt_content: Optional[str]) -> str`, `_prompt_has_breaking_change_marker(prompt_content: Optional[str]) -> bool`, `_iter_breaking_change_directives(prompt_content: Optional[str]) -> List[str]`, `_parse_breaking_change_symbols(directive_tail: str) -> Set[str]`, `_prompt_breaking_change_removed_symbols(prompt_content: Optional[str]) -> Set[str]`, `_prompt_breaking_change_signature_symbols(prompt_content: Optional[str]) -> Set[str]`, `_prompt_allows_breaking_change(prompt_content: Optional[str]) -> bool`, and the regexes `_YAML_FRONT_MATTER_RE`, `_BREAKING_CHANGE_DIRECTIVE_RE`, `_DIRECTIVE_SYMBOL_RE`.

- [ ] **Step 1: Extract the reference**

```bash
{ sed -n '439,454p'  pdd/code_generator_main.py
  sed -n '467,506p'  pdd/code_generator_main.py
  sed -n '513,516p'  pdd/code_generator_main.py
  sed -n '525,626p'  pdd/code_generator_main.py
  sed -n '2403,2405p' pdd/code_generator_main.py; } > /tmp/directives.reference.py
```

- [ ] **Step 2: Author the prompt**

Source text: the `BREAKING-CHANGE` grammar paragraphs inside prompt §5b (`_prompt_breaking_change_removed_symbols` / `_prompt_breaking_change_signature_symbols` bullets, prompt lines 93–131).

Requirements the prompt MUST state:
- Directives are **anchored**: regex `^\s*BREAKING-CHANGE:\s*` with `re.MULTILINE`. Buried mid-line mentions must NOT register.
- Removal verbs: `remove`/`delete`/`drop`/`rename` (+ `-s`/`-d`/`-ing` forms). Signature verbs: `change`/`changes`/`changed`/`changing` followed by `signature`/`signatures`/`api`/`contract`.
- Symbol grammar: comma-separated identifiers, bare or wrapped in **matching** backticks / single quotes / double quotes. Mismatched wrappers rejected. Tokens containing embedded whitespace rejected.
- A bare `BREAKING-CHANGE:` marker must NOT disable any gate globally.
- Follow the `/core` prompt style and the `% Deliverables\n  - Code: pdd/conformance/directives.py` closing.

- [ ] **Step 3: Add the `architecture.json` entry** (`filename: conformance/directives_python.prompt`, `filepath: pdd/conformance/directives.py`, `dependencies: []`, `priority: 5`, `tags: ["conformance","python","directives"]`, interface copied from the prompt).

- [ ] **Step 4: Generate**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/pdd --strength .9 --temperature 0 \
    generate --output pdd/conformance/directives.py \
    pdd/prompts/conformance/directives_python.prompt
```

- [ ] **Step 5: Drift check**

```bash
diff -u /tmp/directives.reference.py pdd/conformance/directives.py | head -100
```

- [ ] **Step 6: Behavioral spot-check**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance.directives import _prompt_breaking_change_removed_symbols as f
assert f('BREAKING-CHANGE: remove old_helper') == {'old_helper'}
assert f('BREAKING-CHANGE: remove old_helper to opt out') == {'old_helper'}, 'prose tokens must be rejected'
assert f('See the BREAKING-CHANGE: marker doc') == set(), 'buried mentions must not register'
assert f('BREAKING-CHANGE: remove \"old_helper\\'') == set(), 'mismatched wrappers must be rejected'
print('OK')
"
```

- [ ] **Step 7: Run the suite; expect the Task 1 baseline.**
- [ ] **Step 8: Commit** — `git commit -m "feat(conformance): extract BREAKING-CHANGE directive parsing into directives.py"`

---

### Task 4: `test_churn.py` — the test-churn gate

**Files:**
- Create: `pdd/prompts/conformance/test_churn_python.prompt`, `pdd/conformance/test_churn.py` (235 lines)
- Modify: `architecture.json`

**Interfaces:**
- Consumes: `pdd.conformance.errors.TestChurnError`, `pdd.conformance.directives._env_flag_enabled`.
- Produces: `_prompt_allows_test_churn(prompt_content: Optional[str]) -> bool`, `_is_python_generation(language: Optional[str], output_path: Optional[str]) -> bool`, `_is_test_output_path(output_path: Optional[str]) -> bool`, `_get_test_churn_threshold() -> float`, `_compute_test_churn_ratio(pre_text: str, post_text: str) -> float`, `_calculate_test_churn_ratio(before: str, after: str) -> float`, `_verify_test_churn(...)`, `_find_default_test_files(tests_dir: Optional[str], code_file_path: Optional[str]) -> List[str]`, `_TEST_CHURN_OPT_OUT_RE`, `_TEST_CHURN_TARGET_RE`, `_TEST_CHURN_BRIDGE_BREAK_RE`.

- [ ] **Step 1: Extract the reference**

```bash
{ sed -n '633,654p'   pdd/code_generator_main.py
  sed -n '657,769p'   pdd/code_generator_main.py
  sed -n '3184,3238p' pdd/code_generator_main.py
  sed -n '3241,3277p' pdd/code_generator_main.py
  sed -n '4315,4335p' pdd/code_generator_main.py; } > /tmp/test_churn.reference.py
```

- [ ] **Step 2: Author the prompt from §5c (prompt lines 132–143, 6,559 chars)** — lift it nearly whole. It MUST retain:
- The full test-path taxonomy: `tests/`, `__tests__/`, singular `__test__/`; `test_` prefix; `_LANGUAGE_TEST_FILE_EXTS` lowercase family; the case-**sensitive** PascalCase JVM/.NET/Swift family; the case-**insensitive** JS/TS `.test.`/`.spec.` family including `.mjs`/`.cjs`.
- The opt-out grammar: an anchored directive pairing an opt-out verb with `tests` **as the verb's direct object**; `BREAKING-CHANGE: drop foo and rewrite tests` opts out, `BREAKING-CHANGE: rewrite docs and update tests` does not.
- `_compute_test_churn_ratio`: stdlib `difflib.unified_diff`; count `+`/`-` lines excluding `+++`/`---`; return `0.0` if nothing removed; else `max(added, removed) / max(len(pre_lines), 1)`, capped at `1.0`; empty pre → `0.0`.
- Threshold parsing: `PDD_TEST_CHURN_THRESHOLD` default `0.40`; accept `"0.40"` or `"40%"`; unparseable logs a warning and falls back to `0.40`; clamp to `[0.0, 1.0]`.
- `PDD_SKIP_TEST_CHURN_GATE=1` disables only this gate; `PDD_SKIP_CONFORMANCE=1` disables all.

- [ ] **Step 3: `architecture.json` entry** — `dependencies: ["conformance/errors_python.prompt", "conformance/directives_python.prompt"]`.

- [ ] **Step 4: Generate**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/pdd --strength .9 --temperature 0 \
    generate --output pdd/conformance/test_churn.py \
    pdd/prompts/conformance/test_churn_python.prompt
```

- [ ] **Step 5: Drift check** — `diff -u /tmp/test_churn.reference.py pdd/conformance/test_churn.py | head -100`

- [ ] **Step 6: Behavioral spot-check**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance.test_churn import _is_test_output_path as p, _compute_test_churn_ratio as r, _get_test_churn_threshold as t
assert p('tests/test_x.py') and p('src/__test__/a.ts') and p('a/FooTests.swift')
assert not p('src/latest.kt'), 'case-sensitive PascalCase family'
assert p('src/a.spec.mjs')
assert r('', 'anything') == 0.0
assert r('a\nb\nc\n', 'a\nb\nc\n') == 0.0
assert t() == 0.40
import os; os.environ['PDD_TEST_CHURN_THRESHOLD']='40%'; assert abs(t()-0.40)<1e-9
os.environ['PDD_TEST_CHURN_THRESHOLD']='invalid'; assert t()==0.40
print('OK')
"
```

- [ ] **Step 7: Run the suite** — note `tests/test_cmd_test_main.py` imports `TestChurnError`; it must still pass unchanged.
- [ ] **Step 8: Commit** — `git commit -m "feat(conformance): extract the test-churn gate into test_churn.py"`

---

### Task 5: `surface.py` — `__all__` resolution and public-surface snapshot

**Files:**
- Create: `pdd/prompts/conformance/surface_python.prompt`, `pdd/conformance/surface.py` (511 lines)
- Modify: `architecture.json`

**Interfaces:**
- Consumes: nothing (stdlib `ast` only, plus `pdd.split_validation.collect_patch_symbols_for_module`).
- Produces: `_collect_bound_module_names(tree) -> Set[str]`, `_scannable_children(node) -> Iterator[ast.AST]`, `_node_writes_dunder_all(node) -> bool`, `_subtree_mutates_dunder_all(node) -> bool`, `_clean_dunder_all_literal(node) -> Optional[Set[str]]`, `_extract_dunder_all(tree) -> Optional[Set[str]]`, `_assign_target_matches(target, symbol) -> bool`, `_symbol_exists_in_module(tree, symbol) -> bool`, `_effective_patch_targets(...)`, `_collect_patch_targets(file_path: Optional[str]) -> Set[str]`, `_reexport_binding(alias) -> Optional[str]`, `_snapshot_public_surface(code_text: str, language: str, file_path: str = None) -> Set[str]`, `_diff_public_surface(pre: Set[str], post: Set[str]) -> List[str]`, `_collect_python_public_surface(source: str) -> List[str]`, `_SCOPE_NODE_TYPES`, `_COMPREHENSION_TYPES`, `_DUNDER_ALL_MUTATOR_METHODS`.

- [ ] **Step 1: Extract the reference**

```bash
{ sed -n '772,822p'   pdd/code_generator_main.py
  sed -n '826,840p'   pdd/code_generator_main.py
  sed -n '843,1131p'  pdd/code_generator_main.py
  sed -n '1134,1311p' pdd/code_generator_main.py
  sed -n '2398,2400p' pdd/code_generator_main.py; } > /tmp/surface.reference.py
```

- [ ] **Step 2: Author the prompt** from the `_snapshot_public_surface` bullets of §5b (prompt lines 93–131). It MUST retain, in full:
- **`__all__` precedence**: authoritative when a clean `ast.Assign`/bound `ast.AnnAssign` of a `List`/`Tuple` of string `Constant`s; a name is public **iff** in `__all__`, even underscore-prefixed; names not in `__all__` are not public. Filter to names actually bound at module scope. **Last clean assignment wins, resolved in SOURCE ORDER.**
- Classes listed in `__all__` contribute **recursively-walked members at every depth**, regardless of underscore prefix.
- A bare `__all__: T` annotation with no value is a no-op; **any other write RESETS to unresolvable**; detection via `_subtree_mutates_dunder_all` descending into `if`/`for`/`while`/`with`/`try`/`match` but NOT into def/class/lambda scopes, and not flagging comprehension targets. Covers AugAssign, mutator methods (but not read-only `.copy()`/`.index()`), subscript/slice store/delete, bare-name store/delete, walrus, pattern/exception captures binding via a STRING field, and imports that BIND `__all__`.
- **Fallback heuristic** (no/unresolvable `__all__`): top-level `FunctionDef`/`AsyncFunctionDef`/`ClassDef`; dotted names for methods and nested classes at every depth; skip dunders; skip single-underscore names at any depth unless patch targets; module-level `Assign`/bound `AnnAssign` with bare-`Name` targets (including Tuple/List/Starred unpacking), capturing `AnnAssign` only when `node.value is not None`.
- **Imports are public surface ONLY as explicit re-exports** — `_reexport_binding(alias)` returns the bound name when `alias.asname is not None and alias.asname == alias.name and not alias.asname.startswith("_")`. Plain imports are implementation detail (issues #1662/#1663/pdd_cloud#2256). Skip `from X import *`. **Skip `from __future__ import …` entirely**, in both `_snapshot_public_surface` and `_collect_bound_module_names`.
- Non-Python languages return `set()`.

- [ ] **Step 3: `architecture.json` entry** — `dependencies: []`.
- [ ] **Step 4: Generate** to `pdd/conformance/surface.py`.
- [ ] **Step 5: Drift check** — `diff -u /tmp/surface.reference.py pdd/conformance/surface.py | head -120`

- [ ] **Step 6: Behavioral spot-check**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance.surface import _snapshot_public_surface as s
assert '_public_helper' in s('__all__=[\"_public_helper\"]\ndef _public_helper():pass\n','python')
assert 'Service.run' in s('__all__=[\"Service\"]\nclass Service:\n  def run(self):pass\n','python')
assert 'annotations' not in s('from __future__ import annotations\n','python')
assert 'Any' not in s('from typing import Any\n','python'), 'plain imports are not surface'
assert 'Any' in s('from typing import Any as Any\n','python'), 'redundant alias IS a re-export'
assert s('def f():pass','javascript') == set()
print('OK')
"
```

- [ ] **Step 7: Run the suite** — `tests/test_issue_67.py` imports `_snapshot_public_surface` and `_collect_patch_targets` from `code_generator_main`; unchanged, must still pass.
- [ ] **Step 8: Commit** — `git commit -m "feat(conformance): extract __all__ resolution and public-surface snapshot into surface.py"`

---

### Task 6: `dataclass_signatures.py` — `@dataclass` constructor synthesis

Sequenced before `signatures.py` because `_snapshot_public_signatures` calls into it.

**Files:**
- Create: `pdd/prompts/conformance/dataclass_signatures_python.prompt`, `pdd/conformance/dataclass_signatures.py` (456 lines)
- Modify: `architecture.json`

**Interfaces:**
- Consumes: nothing (stdlib `ast`).
- Produces: `_is_dataclass_decorator(decorator) -> bool`, `_dataclass_decorator_is_kw_only(decorator) -> bool`, `_dataclass_decorator_synthesizes_init(decorator) -> bool`, `_is_kw_only_sentinel(annotation) -> bool`, `_dataclass_field_call_is_init_false(value) -> bool`, `_collect_dataclass_own_parts(class_node: ast.ClassDef) -> List[str]`, `_part_field_name(part: str) -> Optional[str]`, `_collect_dataclass_inherited_parts(...) -> List[str]`, `_synthesize_dataclass_init_signature(...) -> str`.

- [ ] **Step 1: Extract the reference** — `sed -n '1459,1930p' pdd/code_generator_main.py > /tmp/dataclass_signatures.reference.py`

- [ ] **Step 2: Author the prompt** from the `@dataclass` bullet of §5b. It MUST retain:
- Synthesise the constructor from class-body `ast.AnnAssign` fields in **source order** when there is no explicit `__init__`; an explicit `__init__` always wins.
- `@dataclass(kw_only=True)` (bare `dataclass` and `dataclasses.dataclass` forms) emits a single leading `*`.
- In-body `_: KW_ONLY` sentinel (`KW_ONLY` Name or `dataclasses.KW_ONLY` Attribute) recognised **before** the underscore-prefix skip; fields before stay positional, after become kw-only.
- Decorator **and** sentinel together emit only ONE `*` (decorator wins). A trailing `*` with no kw-only fields after it is stripped so `(*)` never appears.
- `InitVar[...]` fields ARE included; `ClassVar[...]` excluded; `field(init=False, ...)` / `dataclasses.field(init=False, ...)` excluded, but `init=True`, missing `init`, or any non-`field` call keeps the field.
- Inherited fields collected in **REVERSE-MRO order** — for `class C(A, B)` the synth is `(b, a, c)`. A base decorated `@dataclass(init=False)` STILL contributes its fields. Cross-module bases emit a single `[inherited_unresolved]` token. A derived redeclaration wins on annotation/default text but keeps the **base's original position**.

- [ ] **Step 3: `architecture.json` entry** — `dependencies: []`.
- [ ] **Step 4: Generate** to `pdd/conformance/dataclass_signatures.py`.
- [ ] **Step 5: Drift check** — `diff -u /tmp/dataclass_signatures.reference.py pdd/conformance/dataclass_signatures.py | head -120`

- [ ] **Step 6: Behavioral spot-check**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
import ast
from pdd.conformance.dataclass_signatures import _synthesize_dataclass_init_signature as syn
src='''
@dataclass
class A:
    a: int
@dataclass
class B:
    b: int
@dataclass
class C(A, B):
    c: int
'''
tree=ast.parse(src); classes={n.name:n for n in tree.body if isinstance(n,ast.ClassDef)}
sig=syn(classes['C'], classes)
assert sig.index('b')<sig.index('a')<sig.index('c'), f'reverse-MRO order violated: {sig}'
print('OK', sig)
"
```

- [ ] **Step 7: Run the suite.**
- [ ] **Step 8: Commit** — `git commit -m "feat(conformance): extract @dataclass constructor synthesis into dataclass_signatures.py"`

---

### Task 7: `signatures.py` — signature entries and binding kinds

**Files:**
- Create: `pdd/prompts/conformance/signatures_python.prompt`, `pdd/conformance/signatures.py` (596 lines)
- Modify: `architecture.json`

**Interfaces:**
- Consumes: `pdd.conformance.surface` (`_extract_dunder_all`, `_collect_bound_module_names`, `_reexport_binding`, `_effective_patch_targets`), `pdd.conformance.dataclass_signatures._synthesize_dataclass_init_signature`.
- Produces: `_format_python_signature(node, *, skip_first: bool = False) -> str`, `_python_method_binding_kind(node) -> str`, `_python_property_accessor_role(node) -> Optional[str]`, `_resolve_class_node(...)`, `_class_constructor_signature(...)`, `_patch_target_signature_entry(...)`, `_snapshot_public_signatures(...) -> Dict[str, str]`.

- [ ] **Step 1: Extract the reference**

```bash
{ sed -n '1314,1456p' pdd/code_generator_main.py
  sed -n '1933,2032p' pdd/code_generator_main.py
  sed -n '2035,2395p' pdd/code_generator_main.py; } > /tmp/signatures.reference.py
```

- [ ] **Step 2: Author the prompt** from the `_snapshot_public_signatures` bullets of §5b. It MUST retain:
- The **same** `__all__` precedence, class-member recursion, patch-target preservation, explicit-re-export rule and `from __future__` skip as `surface.py` — the two must agree on what is public, or the removed-symbol diff and the signature diff disagree.
- Every entry carries a **leading kind prefix**: `[function]` / `[async_function]` / `[class]` at top level; `[instance]` / `[staticmethod]` / `[classmethod]` / `[property:<roles>]` in classes; `[assignment]` for module-level rebindings; `[import]`, `[import:<module>]`, `[import:from <module>]`, `[import:from <module>:<source>]` for re-exports.
- A **redundant** alias (`asname == name`) canonicalises to the **plain** marker, not the renaming-alias marker — otherwise normalising `from pathlib import Path as Path` → `from pathlib import Path` diffs as a phantom change.
- For `ImportFrom`, the recorded module includes the relative level: `"." * node.level + (node.module or "")`, so `from . import Foo as Foo` → `from .. import Foo as Foo` diffs as `[import:from .]` vs `[import:from ..]`.
- Import entries reach the dict ONLY when public — a clean `__all__` lists the bound name, OR `_reexport_binding(alias)` is non-`None`.

- [ ] **Step 3: `architecture.json` entry** — `dependencies: ["conformance/surface_python.prompt", "conformance/dataclass_signatures_python.prompt"]`.
- [ ] **Step 4: Generate** to `pdd/conformance/signatures.py`.
- [ ] **Step 5: Drift check** — `diff -u /tmp/signatures.reference.py pdd/conformance/signatures.py | head -120`

- [ ] **Step 6: Behavioral spot-check**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance.signatures import _snapshot_public_signatures as sig
d=sig('from pathlib import Path as Path\n','python')
assert d.get('Path')=='[import:from pathlib]', d
d2=sig('from pathlib import Path\n__all__=[\"Path\"]\n','python')
assert d2.get('Path')=='[import:from pathlib]', d2
d3=sig('class C:\n  @property\n  def x(self):pass\n','python')
assert any(v.startswith('[property:') for v in d3.values()), d3
print('OK')
"
```

- [ ] **Step 7: Run the suite** — `tests/test_issue_1558_semantic_contracts.py` and the binding-kind tests must stay green.
- [ ] **Step 8: Commit** — `git commit -m "feat(conformance): extract signature snapshotting into signatures.py"`

---

### Task 8: `declared_surface.py` — the public-surface regression gate

**Files:**
- Create: `pdd/prompts/conformance/declared_surface_python.prompt`, `pdd/conformance/declared_surface.py` (498 lines)
- Modify: `architecture.json`

**Interfaces:**
- Consumes: `pdd.conformance.errors.PublicSurfaceRegressionError`, `pdd.conformance.errors.ArchitectureConformanceError`, `pdd.conformance.surface`, `pdd.conformance.signatures`, `pdd.conformance.directives`, `pdd.interface_semantics` (`signature_entries_compatible`, `build_module_default_symbols`).
- Produces: `_collect_declared_surface(prompt_content: str, prompt_name: str) -> Dict[str, Optional[str]]`, `_declared_signature_to_entry(raw_sig, binding_kind, is_async=..., strip_receiver=...) -> Optional[str]`, `_entry_binding_context(entry: Optional[str]) -> Optional[Tuple[str, bool]]`, `_declared_presence_name(name: str) -> str`, `_declared_patch_targets(...)`, `_verify_public_surface_regression(...)`.

- [ ] **Step 1: Extract the reference** — `sed -n '2408,2915p' pdd/code_generator_main.py > /tmp/declared_surface.reference.py`

- [ ] **Step 2: Author the prompt** from the `#1900` / `#1012` / `#1612` / `#1558` bullets of §5b. It MUST retain:
- **Syntax pre-check (#1612)**: when a pre-generation surface exists, `ast.parse(generated_code)` FIRST; a `SyntaxError` raises `ArchitectureConformanceError` (NOT `PublicSurfaceRegressionError`) with a syntax-focused repair directive, so a truncated generation is not mis-diagnosed as symbol removal.
- **Prompt-declared interface as contract (#1900)**: `type: "module"` only — `cli`/`command` names excluded. Declared top-level functions compared against the DECLARED signature with **both** `old_symbols` and `new_symbols` from `build_module_default_symbols(generated_code)`. Declared dotted methods and `Class.__init__` are receiver-stripped; only symbols with a parseable paren signature join `declared_validated`, and only those are excluded from the old-code baseline.
- **Semantic comparison (#1558)**: use `signature_entries_compatible`, not string equality; per-side default-symbol tables from each module version; do NOT short-circuit on equal text for callables; fall back to exact-string equality only when it returns `None`.
- `BREAKING-CHANGE: change signature <sym>` on a DECLARED symbol relaxes only binding-kind/async, never declared params.
- Message MUST start `Public surface regression for {prompt_name}:` and list `removed:`, `signature_changed:`, `output:`, `pre_surface_size:`, `post_surface_size:` on their own lines. `signature_details` appends one compact `signature_detail: <json>` line per tuple, AFTER the existing fields, which stay byte-identical.
- First-time generation exempt. `PDD_SKIP_PUBLIC_SURFACE_GATE=1` disables only this gate.

- [ ] **Step 3: `architecture.json` entry** — `dependencies: ["conformance/errors_python.prompt", "conformance/surface_python.prompt", "conformance/signatures_python.prompt", "conformance/directives_python.prompt"]`.
- [ ] **Step 4: Generate** to `pdd/conformance/declared_surface.py`.
- [ ] **Step 5: Drift check** — `diff -u /tmp/declared_surface.reference.py pdd/conformance/declared_surface.py | head -120`

- [ ] **Step 6: Message-format check**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance.errors import PublicSurfaceRegressionError as E
e=E('p.prompt','out.py',['gone'],5,4,signature_details=[('s','a','b','pdd-interface')])
m=str(e)
assert m.startswith('Public surface regression for p.prompt:'), m[:70]
for f in ('removed:','signature_changed:','output:','pre_surface_size:','post_surface_size:','signature_detail:'):
    assert f in m, f
print('OK')
"
```

- [ ] **Step 7: Run the suite** — `tests/test_issue_67_expansion.py` and `test_issue_1558_semantic_contracts.py` are the sharpest checks here.
- [ ] **Step 8: Commit** — `git commit -m "feat(conformance): extract the public-surface regression gate into declared_surface.py"`

---

### Task 9: `annotation_reconcile.py` — deterministic annotation reconciliation (#1968)

**Files:**
- Create: `pdd/prompts/conformance/annotation_reconcile_python.prompt`, `pdd/conformance/annotation_reconcile.py` (250 lines)
- Modify: `architecture.json`

**Interfaces:**
- Consumes: `pdd.conformance.declared_surface._collect_declared_surface`, `pdd.interface_semantics.annotations_compatible`.
- Produces: `_index_function_defs(tree) -> Dict[str, ast.AST]`, `_parse_declared_def(raw_signature: Optional[str]) -> Optional[ast.FunctionDef]`, `_signature_slots(...)`, `_line_start_byte_offsets(source: str) -> List[int]`, `_node_byte_span(...)`, `_apply_byte_edits(source: str, edits: List[Tuple[int,int,str]]) -> str`, `_annotation_only_edits(...)`, `_reconcile_declared_annotation_drift(existing_code, generated_code, prompt_name, output_path, language, prompt_content) -> Optional[str]`.

- [ ] **Step 1: Extract the reference** — `sed -n '2918,3181p' pdd/code_generator_main.py > /tmp/annotation_reconcile.reference.py`

- [ ] **Step 2: Author the prompt** from the `#1968` bullet of §5b. It MUST retain:
- Runs immediately BEFORE the public-surface gate; when it returns non-`None`, that string is what the gate checks and the writer persists.
- Rewrites only when a declared `type: "module"` symbol's generated signature differs from the declaration **ONLY** in annotation spelling — identical parameter names, order, kinds and defaults, and only annotations `annotations_compatible` deems INCOMPATIBLE.
- Rewrite is a **UTF-8 byte-offset splice** on the emitted annotation node.
- **Fail-safe**: any structural drift disqualifies that symbol; a compatible alias (`Dict` vs `dict`) is never churned; the whole rewrite is discarded if the reconciled source no longer parses.
- Returns `None` unless at least one annotation was reconciled. `PDD_SKIP_ANNOTATION_RECONCILE=1` bypasses it.

- [ ] **Step 3: `architecture.json` entry** — `dependencies: ["conformance/declared_surface_python.prompt"]`.
- [ ] **Step 4: Generate** to `pdd/conformance/annotation_reconcile.py`.
- [ ] **Step 5: Drift check** — `diff -u /tmp/annotation_reconcile.reference.py pdd/conformance/annotation_reconcile.py | head -100`

- [ ] **Step 6: Behavioral spot-check — the no-op guarantee**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance.annotation_reconcile import _reconcile_declared_annotation_drift as rec
out = rec('', 'def f(x: int) -> None:\n    pass\n', 'p.prompt', 'o.py', 'python', '')
assert out is None, 'must be a no-op when there is nothing to reconcile'
print('OK')
"
```

- [ ] **Step 7: Run the suite** — `tests/test_issue_1968_annotation_convergence.py` is the direct check.
- [ ] **Step 8: Commit** — `git commit -m "feat(conformance): extract annotation reconciliation into annotation_reconcile.py"`

---

### Task 10: `interface_check.py` — architecture and `<pdd-interface>` conformance

**Files:**
- Create: `pdd/prompts/conformance/interface_check_python.prompt`, `pdd/conformance/interface_check.py` (734 lines)
- Modify: `architecture.json`

**Interfaces:**
- Consumes: `pdd.conformance.errors.ArchitectureConformanceError`, `pdd.interface_semantics` (`annotations_compatible`, `compare_default_sources`, `build_module_default_symbols`).
- Produces: `_collect_python_symbols(body, prefix) -> List[str]`, `_parse_declared_param_names(signature: str) -> Optional[List[str]]`, `_collect_actual_param_names(func_node) -> List[str]`, `ParamSpec`, `_ast_args_to_specs(args) -> List[ParamSpec]`, `_parse_declared_param_specs(signature: str) -> Optional[List[ParamSpec]]`, `_collect_actual_param_specs(func_node) -> List[ParamSpec]`, `_find_target_function(...)`, `_extract_pdd_interface_signatures(...)`, `_collect_pdd_interface_names(prompt_content: Optional[str]) -> Set[str]`, `_verify_pdd_interface_signatures(...)`, `_verify_architecture_conformance(...)`, `_verify_architecture_json_conformance(...)`.

- [ ] **Step 1: Extract the reference**

```bash
{ sed -n '3485,3573p' pdd/code_generator_main.py
  sed -n '3581,3635p' pdd/code_generator_main.py
  sed -n '3638,4247p' pdd/code_generator_main.py; } > /tmp/interface_check.reference.py
```

- [ ] **Step 2: Author the prompt** from §5 (prompt lines 66–91, 10,445 chars) plus the Architecture-Logic paragraph of `% Instructions`. It MUST retain:
- Three inspected `<pdd-interface>` shapes: `type: "module"` (`module.functions`), `type: "cli"` (`cli.commands`), `type: "command"` (`command.commands`, or a single `command` dict). Entries omitting `signature` are silent no-ops.
- Dotted declarations (`ContentSelector.select`) resolved by descending nested `ClassDef` nodes then matching the final segment as a `def`/`async def`.
- Three checks in priority order: **missing function/method** → bare names in `missing_funcs`; **missing parameter** → dotted `func.param` in `missing_params`, with `**kwargs`/`*args` NOT satisfying a declared named parameter; **signature drift** → annotation drift only when BOTH sides annotate and they are not `annotations_compatible`; default drift raised when declared default is dropped (`<no default>` sentinel) or `compare_default_sources` returns `INCOMPATIBLE` **or** `UNKNOWN` (fail closed), suppressed only on `COMPATIBLE`.
- Each category in its **own sentence**: `declares function(s)/method(s) missing from the generated code: ...`, `declares parameter(s) missing from the generated code: ...`, `declares parameter(s) whose signature drifted in the generated code: <func.param> (<kind>: declared \`<src>\`, found \`<src>\`), ...`.
- `repair_directive` groups dotted method params with **`rpartition('.')`, not `partition('.')`**, so `ContentSelector.select.mode` attributes to function `ContentSelector.select` / param `mode`.
- camelCase guard exempts names declared in EITHER `architecture.json` `module.functions` OR the prompt's own `<pdd-interface>` (via `_collect_pdd_interface_names`, which includes description-only declarations and so must NOT reuse the signature-gated `_extract_pdd_interface_signatures`). Issue #1446.
- Do NOT descend into `if`/`try`/`with` inside class bodies.
- Missing `<pdd-interface>` → skip silently; malformed JSON → `logger.warning` and skip, never raise.
- Message MUST start `Architecture conformance error for {prompt_name}:`.

- [ ] **Step 3: `architecture.json` entry** — `dependencies: ["conformance/errors_python.prompt"]`.
- [ ] **Step 4: Generate** to `pdd/conformance/interface_check.py`.
- [ ] **Step 5: Drift check** — `diff -u /tmp/interface_check.reference.py pdd/conformance/interface_check.py | head -120`

- [ ] **Step 6: Behavioral spot-check — the `rpartition` trap**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance.errors import ArchitectureConformanceError as E
e=E('p.prompt','o.py',{},['ContentSelector.select'],[],['ContentSelector.select.mode'])
d=e.repair_directive
assert 'ContentSelector.select' in d and 'ContentSelector.select.mode' not in d.replace('ContentSelector.select.mode',''), d[:200]
assert str(e).startswith('Architecture conformance error for p.prompt:')
print('OK')
"
```

- [ ] **Step 7: Run the suite** — `tests/test_prompt_contract_validation.py` and `test_checkup_interactive_session.py::_verify_pdd_interface_signatures` are the direct checks.
- [ ] **Step 8: Commit** — `git commit -m "feat(conformance): extract architecture and pdd-interface conformance into interface_check.py"`

---

### Task 11: Checkpoint — Phase 1 complete, full suite

Nothing yet imports `pdd/conformance/`. `code_generator_main.py` is byte-identical to `main`. The suite must therefore be **exactly** the Task 1 baseline. If it is not, a new module has a side effect at import time — find it before proceeding.

**Files:** none modified.

- [ ] **Step 1: Confirm the orchestrator is untouched**

```bash
git diff --stat main -- pdd/code_generator_main.py
```

Expected: empty output.

- [ ] **Step 2: Full suite**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -m pytest -q -p no:randomly tests/ 2>&1 | tail -15
```

- [ ] **Step 3: Verify no conformance module imports the orchestrator**

```bash
grep -rn "code_generator_main" pdd/conformance/ && echo "VIOLATION - circular dependency" || echo "OK - no back-reference"
```

- [ ] **Step 4: Verify total extracted size**

```bash
wc -l pdd/conformance/*.py
```

Expected ≈ 3,784 lines across the nine modules (±10% is fine; a module more than 25% off its spec size signals the prompt drifted).

- [ ] **Step 5: Commit the checkpoint**

```bash
git commit --allow-empty -m "chore(conformance): phase 1 checkpoint - nine modules generated, suite green"
```

---

### Task 12: Switch the orchestrator prompt over

The riskiest task. Hazards H1, H2 and H3 all land here. Do not split it — the prompt, its `<pdd-interface>`, its selector and the `architecture.json` entry must change together or the module fails its own gates.

**Files:**
- Modify: `pdd/prompts/code_generator_main_python.prompt` (remove §5/5a/5b/5c, fix line 168 selector, fix `<pdd-interface>`, add `<pdd-dependency>` lines, add re-export + BREAKING-CHANGE instructions)
- Modify: `architecture.json` (the `code_generator_main_python.prompt` entry)

**Interfaces:**
- Consumes: all nine conformance modules.
- Produces: an orchestrator prompt of roughly 29% its former size.

- [ ] **Step 1: Remove the 25 moved symbols from the line-168 selector**

Keep exactly these 11: `def:code_generator_main`, `def:_run_discovery`, `def:_should_wire_generated_exports`, `def:_wire_to_parent_init`, `def:_parse_front_matter`, `def:_expand_vars`, `def:_run_git_command`, `def:is_git_repository`, `def:get_git_content_at_ref`, `def:get_file_git_status`, `def:git_add_files`.

Remove: `pattern:^ParamSpec\s*=`, `class:ArchitectureConformanceError`, `class:PublicSurfaceRegressionError`, `class:TestChurnError`, `class:ProseOutputError`, `def:_verify_architecture_conformance`, `def:_verify_architecture_json_conformance`, `def:_verify_pdd_interface_signatures`, `def:_extract_pdd_interface_signatures`, `def:_collect_declared_surface`, `def:_declared_signature_to_entry`, `def:_declared_presence_name`, `def:_declared_patch_targets`, `def:_entry_binding_context`, `def:_class_constructor_signature`, `def:_resolve_class_node`, `def:_symbol_exists_in_module`, `def:_patch_target_signature_entry`, `def:_parse_declared_param_names`, `def:_collect_actual_param_names`, `def:_parse_declared_param_specs`, `def:_collect_actual_param_specs`, `def:_ast_args_to_specs`, `def:_find_target_function`, `def:_collect_python_symbols`.

- [ ] **Step 2: Verify the selector resolves**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
import re
line = open('pdd/prompts/code_generator_main_python.prompt').read().split('\n')[167]
syms = re.search(r'select=\"([^\"]*)\"', line).group(1).split(',')
print('remaining:', len(syms))
assert len(syms) == 11, syms
src = open('pdd/code_generator_main.py').read()
for s in syms:
    name = s.split(':',1)[1]
    assert re.search(rf'def {re.escape(name)}\b', src), f'selector references missing symbol: {name}'
print('OK - all 11 resolve')
"
```

- [ ] **Step 3: Remove the four exception entries from `<pdd-interface>`**

Leave exactly `is_git_repository`, `get_git_content_at_ref`, `get_file_git_status`, `git_add_files`, `code_generator_main`.

- [ ] **Step 4: Remove prompt sections 5, 5a, 5b, 5c** and the Deliverables items describing the moved helpers and exception classes. Keep sections 1, 2, 3, 4, 6 and the orchestration parts of `% Instructions`.

- [ ] **Step 5: Add `<pdd-dependency>` lines** for all nine conformance prompts, alongside the existing ones.

- [ ] **Step 6: Add the re-export requirement (H3)** to the prompt's Requirements:

```
- **Re-export the conformance gate surface.** Import the gate entry points from
  `pdd.conformance` and re-export the four typed exceptions using the REDUNDANT
  ALIAS form so they register as explicit re-exports rather than removals:
      from .conformance.errors import ArchitectureConformanceError as ArchitectureConformanceError
      from .conformance.errors import ProseOutputError as ProseOutputError
      from .conformance.errors import PublicSurfaceRegressionError as PublicSurfaceRegressionError
      from .conformance.errors import TestChurnError as TestChurnError
  A plain `from ... import X` is NOT public surface under this module's own
  public-surface rules and would be read as symbol removal.
```

- [ ] **Step 7: Add the one-time BREAKING-CHANGE line** to the prompt body — the `[class]` → `[import:from …]` binding-kind flip is a signature change the gate is specified to diff:

```
BREAKING-CHANGE: change signature ArchitectureConformanceError, PublicSurfaceRegressionError, TestChurnError, ProseOutputError
```

- [ ] **Step 8: Update the `architecture.json` orchestrator entry** — remove the four exception entries from its `interface.module.functions`; append the nine `conformance/*_python.prompt` names to its `dependencies` array.

- [ ] **Step 9: Verify architecture.json is well-formed and consistent**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
import json
d=json.load(open('architecture.json'))
byname={e['filename']:e for e in d}
cg=byname['code_generator_main_python.prompt']
names=[f['name'] for f in cg['interface']['module']['functions']]
assert names==['is_git_repository','get_git_content_at_ref','get_file_git_status','git_add_files','code_generator_main'], names
conf=[k for k in byname if k.startswith('conformance/')]
assert len(conf)==9, conf
for c in conf: assert c in cg['dependencies'], f'missing dep: {c}'
print('OK -', len(d), 'entries,', len(conf), 'conformance')
"
```

- [ ] **Step 10: Commit** (prompt + architecture only; regeneration is Task 13)

```bash
git add pdd/prompts/code_generator_main_python.prompt architecture.json
git commit -m "refactor(prompt): move the gate sections out of code_generator_main_python.prompt"
```

---

### Task 13: Regenerate the orchestrator

**Files:**
- Modify: `pdd/code_generator_main.py` (regenerated, 5,879 → ~2,100 lines)

**Interfaces:**
- Consumes: the Task 12 prompt.
- Produces: an orchestrator that re-exports the four exceptions and delegates to `pdd.conformance`.

- [ ] **Step 1: Snapshot the pre-generation surface for comparison**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance.surface import _snapshot_public_surface as s
import json
print(json.dumps(sorted(s(open('pdd/code_generator_main.py').read(),'python')), indent=0))
" > /tmp/cgm.surface.before.json
wc -l /tmp/cgm.surface.before.json
```

- [ ] **Step 2: Generate**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/pdd --strength .9 --temperature 0 \
    generate --output pdd/code_generator_main.py \
    pdd/prompts/code_generator_main_python.prompt
```

- [ ] **Step 3: Verify the re-exports use the redundant-alias form**

```bash
grep -n "from .conformance.errors import" pdd/code_generator_main.py
```

Expected: four lines, each of the form `import X as X`. A plain `import X` here fails the gate on the next sync — fix the prompt and regenerate, do not hand-edit.

- [ ] **Step 4: Compare public surface**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance.surface import _snapshot_public_surface as s
import json
after = set(s(open('pdd/code_generator_main.py').read(),'python'))
before = set(json.load(open('/tmp/cgm.surface.before.json')))
print('removed:', sorted(before-after))
print('added:  ', sorted(after-before))
"
```

Expected `removed: []`. The four exceptions must still appear, now as re-exports.

- [ ] **Step 5: Verify size and that nothing moved back**

```bash
wc -l pdd/code_generator_main.py   # expect ~2,100
grep -c "class ArchitectureConformanceError\|def _snapshot_public_surface\|def _verify_test_churn" pdd/code_generator_main.py
```

Expected `0` — any non-zero means a gate symbol was regenerated back into the orchestrator; fix the prompt.

- [ ] **Step 6: Full suite**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -m pytest -q -p no:randomly tests/ 2>&1 | tail -15
```

- [ ] **Step 7: Commit**

```bash
git add pdd/code_generator_main.py
git commit -m "refactor(codegen): regenerate code_generator_main from the split prompt"
```

---

### Task 14: Repoint consumers and the silent churn-nonce seam

**Files:**
- Modify: `pdd/agentic_test_generate.py` (drop the lazy import at :109), `pdd/checkup_review_loop.py` (drop the lazy import at :8400), `pdd/one_session_sync.py`, `pdd/cmd_test_main.py`, `pdd/sync_orchestration.py`, `pdd/sync_main.py`, `pdd/server/routes/prompts.py`
- Modify: `tests/test_code_generator_main.py` (H4)

**Interfaces:**
- Consumes: `pdd.conformance.*`.
- Produces: no remaining lazy imports of `code_generator_main` for gate symbols.

- [ ] **Step 1: Fix the silent seam first (H4)**

In `tests/test_code_generator_main.py`, the nonce cache is reset by direct module-attribute assignment, not `patch()`:

```python
import pdd.code_generator_main as cg
cg._CHURN_NONCE_CACHE = None
cg._CHURN_NONCE_READ = False
```

Repoint to where the globals now live:

```python
import pdd.conformance.errors as cgerr
cgerr._CHURN_NONCE_CACHE = None
cgerr._CHURN_NONCE_READ = False
```

- [ ] **Step 2: Prove the seam is live** — the check that it is testing something again:

```bash
# Temporarily break the nonce reader, confirm the test FAILS, then restore.
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -m pytest -q -p no:randomly \
    tests/test_code_generator_main.py -k nonce 2>&1 | tail -5
```

Expected: passes now. Then edit `pdd/conformance/errors.py` `_read_churn_nonce` to `return ""` unconditionally, re-run, and confirm it **FAILS**. Restore by regenerating from the prompt. If it still passes with the reader broken, the repoint in Step 1 did not take.

- [ ] **Step 3: Repoint gate imports in the six production consumers**

```bash
grep -rn "from .code_generator_main import\|from pdd.code_generator_main import" \
    pdd/one_session_sync.py pdd/sync_orchestration.py pdd/cmd_test_main.py \
    pdd/agentic_test_generate.py pdd/sync_main.py pdd/server/routes/prompts.py pdd/checkup_review_loop.py
```

Repoint per the spec's mapping: exceptions → `from .conformance import ...`; `_verify_test_churn` / `_get_test_churn_threshold` / `_prompt_allows_test_churn` / `_is_test_output_path` / `_find_default_test_files` → `from .conformance.test_churn import ...`; `_env_flag_enabled` → `from .conformance.directives import ...`; `_verify_public_surface_regression` → `from .conformance.declared_surface import ...`. Leave `code_generator_main` itself alone.

- [ ] **Step 4: Remove the two circular-import workarounds**

`pdd/agentic_test_generate.py:109` ("to avoid a circular dependency") and `pdd/checkup_review_loop.py:8400` ("Lazy imports: code_generator_main pulls in the heavy generation…") can become module-level imports from `pdd.conformance`, which has no back-reference.

- [ ] **Step 5: Confirm no cycle**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
import pdd.conformance, pdd.agentic_test_generate, pdd.checkup_review_loop, pdd.one_session_sync
print('OK - imports clean at module level')
"
grep -rn "code_generator_main" pdd/conformance/ && echo VIOLATION || echo "OK"
```

- [ ] **Step 6: Full suite**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -m pytest -q -p no:randomly tests/ 2>&1 | tail -15
```

- [ ] **Step 7: Commit**

```bash
git add pdd/ tests/test_code_generator_main.py
git commit -m "refactor: repoint gate consumers at pdd.conformance and drop the lazy-import workarounds"
```

---

### Task 15: Final verification

**Files:** none modified (except a possible `.pdd/meta` fingerprint refresh).

- [ ] **Step 1: Import-surface check — all 28 external symbols**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
import importlib, ast, pathlib
wanted=set()
for p in list(pathlib.Path('pdd').rglob('*.py'))+list(pathlib.Path('tests').rglob('*.py'))+list(pathlib.Path('context').rglob('*.py')):
    if p.name=='code_generator_main.py': continue
    try: t=ast.parse(p.read_text())
    except Exception: continue
    for n in ast.walk(t):
        if isinstance(n,ast.ImportFrom) and n.module and n.module.endswith('code_generator_main'):
            for a in n.names: wanted.add(a.name)
m=importlib.import_module('pdd.code_generator_main')
missing=[w for w in sorted(wanted) if not hasattr(m,w)]
print('still imported from code_generator_main:', len(wanted))
print('MISSING:', missing)
assert not missing, missing
print('OK')
"
```

Every name still imported from `code_generator_main` must resolve. Anything listed as MISSING needs either a re-export in the prompt or a repointed consumer.

- [ ] **Step 2: Gate self-check — the module must pass its own gates**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/pdd sync code_generator_main --dry-run --json 2>&1 | tail -20
```

Expected: no `PublicSurfaceRegressionError`, no `ArchitectureConformanceError`. This is the H1/H2/H3 acceptance check.

- [ ] **Step 3: Message-format contract**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -c "
from pdd.conformance.errors import *
from pdd.conformance.errors import ArchitectureConformanceError as A, PublicSurfaceRegressionError as P, TestChurnError as T, ProseOutputError as R
assert str(A('p','o',{},[],[],['x'])).startswith('Architecture conformance error for p:')
assert str(P('p','o',['x'],1,0)).startswith('Public surface regression for p:')
assert str(T('p','o',0.9,0.4,10,1)).startswith('Test churn threshold exceeded for p:')
assert str(R('p','o','python')).startswith('Generation output extraction failure for p:')
print('OK - all four cross-process prefixes intact')
"
```

- [ ] **Step 4: Full suite, final**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -m pytest -q -p no:randomly tests/ 2>&1 | tail -15
```

Must match the Task 1 baseline counts (plus any new `tests/conformance/` tests).

- [ ] **Step 5: Lint**

```bash
/opt/homebrew/Caskroom/miniconda/base/envs/pdd/bin/python -m pylint pdd/conformance/ 2>&1 | tail -20
```

- [ ] **Step 6: Refresh `.pdd/meta` fingerprints if `pdd sync --dry-run` reports drift**

Only if Step 2 reported a stale fingerprint. Follow the pattern of commit `16a48378c`: record the current consistent state, and state in the commit message that it is local bookkeeping only.

- [ ] **Step 7: Final commit**

```bash
git commit --allow-empty -m "chore(conformance): final verification - suite green, gates pass, 28 import surfaces intact"
```

---

## Self-Review Notes

**Spec coverage:** Layout → Task 1. Nine modules → Tasks 2–10. Consumer API/`__init__.py` → Tasks 1, 2. Prompt decomposition → Tasks 2–10, 12. Dependency direction → Tasks 11, 14. H1 → Task 12 Steps 1–2. H2 → Task 12 Steps 3, 8, 9. H3 → Task 12 Steps 6–7, Task 13 Step 3. H4 → Task 14 Steps 1–2. H5 → no action needed (verified: all 27 patch targets stay in the orchestrator); covered by the full-suite runs. H6 → pre-existing, noted only. Registration checklist → Task 1 (`.pddrc`, `__init__.py`) and each module task (prompt, `architecture.json`). Verification → Tasks 11, 15.

**Deferred from the spec, deliberately:** `context/conformance/*_example.py` and `tests/conformance/test_*.py` are not generated by this plan. `/core` covers only 6 of 9 modules with examples and 3 of 9 with tests, and the spec says to add them where they earn their place. Add them in a follow-up once the modules have settled, so a churning prompt does not drag a test file with it.

**Known gap:** Task 2's prompt is composed from interleaved fragments rather than lifted whole, so it is the most likely to need a second regeneration pass. It is also the module everything else depends on — budget extra time there, and do not proceed to Task 3 until its diff is clean.
