# Extracting the conformance gate layer out of `code_generator_main`

Date: 2026-08-06
Branch: `split/cgm-shared-layer` (worktree, based on `feat/language-validity-gate` @ `16a48378c`)

## Problem

`pdd/code_generator_main.py` is 5,949 lines and its prompt is 74 KB / ~30k tokens.

Size alone does not justify surgery — it is only the 6th largest module in `pdd/`,
below five files the project has consciously left flat (`checkup_review_loop.py`
10,336, `agentic_common.py` 10,128, `llm_invoke.py` 7,408,
`sync_determine_operation.py` 7,024, `agentic_checkup_orchestrator.py` 6,463).

The actual defect is a **role collision**. The module is two things at once:

1. A CLI orchestration pipeline (`code_generator_main`, 1,489 lines).
2. A conformance gate/validation library that four other production modules depend on.

The second role is the larger one — ~4,060 lines of code and ~72% of the prompt —
and it is consumed across the codebase:

| Symbol | Imported by |
|---|---|
| `_verify_public_surface_regression` | `sync_orchestration`, `one_session_sync` |
| `_verify_test_churn`, `_get_test_churn_threshold`, `_prompt_allows_test_churn` | `cmd_test_main`, `agentic_test_generate`, `one_session_sync` |
| `_is_test_output_path`, `_env_flag_enabled` | `agentic_test_generate`, `one_session_sync` |
| `_find_default_test_files` | `server/routes/prompts.py` |
| the 5 typed exceptions | `sync_main`, `sync_orchestration`, `one_session_sync`, `cmd_test_main`, `agentic_test_generate` |

Two consumers have resorted to lazy imports with explicit circular-dependency
comments, which is the smoking gun:

- `pdd/agentic_test_generate.py:109` — "to avoid a circular dependency"
- `pdd/checkup_review_loop.py:8400` — "Lazy imports: code_generator_main pulls in the heavy generation…"

`pdd split --intent reduce --propose-only` independently diagnosed this as
`split_shared_layer` (confidence 0.75) and cited the precedent below.

## Precedent

`pdd/interface_semantics.py` was extracted from this exact file in June 2026,
grew to 1,111 lines absorbing the churn, and has since dropped off the target's
co-change list entirely. `code_generator_main` imports from it today.

`pdd/core/` is the house pattern for a grouped subsystem: a folder of flat
modules, one small prompt each, plus a hand-written `__init__.py` that
re-exports with an explicit `__all__`.

| `pdd/core/*.py` | lines | prompt lines |
|---|---|---|
| `__init__.py` | 33 | *(hand-written)* |
| `llm_trace.py` | 104 | *(hand-written)* |
| `remote_session.py` | 61 | 22 |
| `utils.py` | 118 | 54 |
| `errors.py` | 264 | 55 |
| `cloud.py` | 346 | 72 |
| `duplicate_cli_guard.py` | 378 | 84 |
| `dump.py` | 740 | 88 |
| `cli.py` | 1,200 | 95 |

Prompts of 22–95 lines are the target shape. Not every file needs a prompt.

## Goals

- **Split the prompt.** Decompose `code_generator_main_python.prompt` into a set
  of small prompts under `pdd/prompts/conformance/`, following `/core`.
- **Generate the code from those prompts** via `pdd sync`. The regenerated
  modules must behave the same as today's monolith.
- Reduce the orchestrator prompt from ~30k tokens to a set of small prompts.
- Dissolve both circular-import workarounds (a consequence of the above, not a
  separate workstream).

## Generation mode: prompt-only

Decided: **prompts are the source of truth; `pdd sync` produces the `.py` files.**
No hand-authoring of the generated modules, no verbatim code moves.

This matches the repo norm — of 114 `.pdd/meta/*.json` fingerprints, 113 record a
PDD-driven command (`fix` 31, `test` 28, `regenerate-public` 4, `sync`/`update` 6,
`?` 40) and only `code_generator_main_python` records `manual`.

**Accepted risk, recorded deliberately.** This module has never been produced by
`pdd generate` in its current form — commit `16a48378c` states that
`code_generator_main.py` and its prompt "were hand-authored together
(LanguageMismatchError etc. never went through `pdd generate`)". Regeneration
therefore asks the model to re-derive ~4,000 lines of intricate AST logic from
prose: `__all__` source-order resolution, reverse-MRO dataclass `__init__`
synthesis, byte-offset annotation splicing. The R5c section is 31,877 characters
precisely because that logic resists specification.

Drift, if it occurs, will be quiet rather than loud. The test suite is the only
net, which is why the Verification section below is the load-bearing part of this
plan and why per-module regeneration (not a big-bang sync) is required.

## Non-goals

- Anything beyond splitting the prompt and regenerating from it. Consumer import
  updates and test repointing are in scope only where the split strictly forces
  them; they are not a separate refactor.

- Splitting the `code_generator_main` function itself into pipeline phases.
  The `pdd split` proposal's top option (`full_decomposition_flat_siblings`,
  12 modules, parent → 774 lines) does this. It touches 78 files and rewires
  collaborator injection that keeps 27 `patch("pdd.code_generator_main.X")`
  call sites alive. Deferred; see "Follow-on work".
- Splitting `tests/test_code_generator_main.py` (11,888 lines). Test migration
  is limited to what the extraction strictly requires.
- Fixing the `pdd split` step-5 parse bug. Filed separately; see "Related defects".

## Design

### Layout

```
pdd/conformance/
    __init__.py                  hand-written, re-exports + __all__
    errors.py                    ~390
    directives.py                ~230
    test_churn.py                ~290
    surface.py                   ~540
    signatures.py                ~600
    dataclass_signatures.py      ~470
    declared_surface.py          ~510
    annotation_reconcile.py      ~270
    interface_check.py           ~760

pdd/prompts/conformance/
    <one *_python.prompt per module above, except __init__.py>

context/conformance/
    <one *_example.py per module, where warranted>

tests/conformance/
    <one test_*.py per module, where warranted>
```

This mirrors `/core` exactly: `pdd/core/` + `pdd/prompts/core/` +
`context/core/` + `tests/core/`, with a `core:` block in `.pddrc` binding them
(`generate_output_path`, `test_output_path`, `example_output_path`, `prompts_dir`).

`pdd/code_generator_main.py` retains ~1,900 lines: the orchestrator function,
git helpers, front-matter/var expansion, and wiring.

### Consumer-facing API

Follows `pdd/core/`'s actual convention, which is **direct module imports**, with
`__init__.py` re-exporting only the hottest module's surface.

`pdd/core/__init__.py` re-exports `.cloud` symbols and nothing else; every other
core module is imported by path (`from .core.errors import handle_error`,
`from .core.llm_trace import …`, `from .core.cli import …`, `from .core.utils import …`).
Even `cloud` is mostly imported directly — 12 `from .core.cloud import` vs a
handful through the package.

We mirror that: `errors.py` is our `cloud.py` (imported by 5 consumers, the widest
surface), so `pdd/conformance/__init__.py` re-exports the 5 typed exceptions with
an explicit `__all__`. Everything else is imported by path.

| Consumer import | Provides |
|---|---|
| `from .conformance import TestChurnError, …` | the 5 typed exceptions (via `__init__.py`) |
| `from .conformance.test_churn import _verify_test_churn, …` | churn gate + predicates |
| `from .conformance.declared_surface import _verify_public_surface_regression` | public-surface gate |
| `from .conformance.interface_check import _verify_architecture_conformance, …` | architecture + `pdd-interface` checks |

Trade-off, accepted: direct imports bind consumers to file names, so moving a
symbol between conformance modules later is a breaking change for them. This is
the cost of matching the house pattern, and `/core` has lived with it fine.

### Module contents

Line spans refer to `pdd/code_generator_main.py` at `16a48378c`.

**`errors.py`** — `PROSE_OUTPUT_REPAIR_DIRECTIVE` (87–91), `ArchitectureConformanceError`
(94–165), `PublicSurfaceRegressionError` (168–291), `_CHURN_NONCE_ENV` /
`_CHURN_NONCE_CACHE` / `_CHURN_NONCE_READ` (294–296), `_read_churn_nonce` (299–334),
`TestChurnError` (337–396), `ProseOutputError` (399–437), `LanguageMismatchError`
(440–474), `_verify_language_validity` (477–490).

**`directives.py`** — `_parse_llm_bool` (494–502), `_env_flag_enabled` (504–509),
`_YAML_FRONT_MATTER_RE` / `_strip_yaml_front_matter` (522–555),
`_prompt_has_breaking_change_marker` (558–561), `_BREAKING_CHANGE_DIRECTIVE_RE` /
`_DIRECTIVE_SYMBOL_RE` (568–586), `_iter_breaking_change_directives` (589–609),
`_parse_breaking_change_symbols` (612–633), `_prompt_breaking_change_removed_symbols`
(636–657), `_prompt_breaking_change_signature_symbols` (660–681),
`_prompt_allows_breaking_change` (2458–2460).

**`test_churn.py`** — `_LANGUAGE_TEST_FILE_EXTS` (73–85), `_TEST_CHURN_*` regexes
(688–709), `_prompt_allows_test_churn` (712–747), `_is_python_generation` (750–754),
`_is_test_output_path` (757–824), `_get_test_churn_threshold` (3239–3270),
`_compute_test_churn_ratio` (3273–3288), `_calculate_test_churn_ratio` (3291–3293),
`_verify_test_churn` (3296–3332), `_find_default_test_files` (4370–4390).

**`surface.py`** — `_collect_bound_module_names` (827–877), `_SCOPE_NODE_TYPES` /
`_COMPREHENSION_TYPES` / `_DUNDER_ALL_MUTATOR_METHODS` (881–895), `_scannable_children`
(898–927), `_node_writes_dunder_all` (930–979), `_subtree_mutates_dunder_all` (982–990),
`_clean_dunder_all_literal` (993–1017), `_extract_dunder_all` (1020–1079),
`_assign_target_matches` (1082–1090), `_symbol_exists_in_module` (1093–1131),
`_effective_patch_targets` (1134–1147), `_collect_patch_targets` (1150–1154),
`_reexport_binding` (1157–1186), `_snapshot_public_surface` (1189–1361),
`_diff_public_surface` (1364–1366), `_collect_python_public_surface` (2453–2455).

**`signatures.py`** — `_format_python_signature` (1369–1434), `_python_method_binding_kind`
(1437–1486), `_python_property_accessor_role` (1489–1511), `_resolve_class_node`
(1988–2009), `_class_constructor_signature` (2012–2046), `_patch_target_signature_entry`
(2049–2087), `_snapshot_public_signatures` (2090–2450).

**`dataclass_signatures.py`** — `_is_dataclass_decorator` (1514–1547),
`_dataclass_decorator_is_kw_only` (1550–1569), `_dataclass_decorator_synthesizes_init`
(1572–1607), `_is_kw_only_sentinel` (1610–1625), `_dataclass_field_call_is_init_false`
(1628–1663), `_collect_dataclass_own_parts` (1666–1727), `_part_field_name` (1730–1743),
`_collect_dataclass_inherited_parts` (1746–1834), `_synthesize_dataclass_init_signature`
(1837–1985).

**`declared_surface.py`** — `_collect_declared_surface` (2463–2506),
`_declared_signature_to_entry` (2509–2572), `_entry_binding_context` (2575–2588),
`_declared_presence_name` (2591–2602), `_declared_patch_targets` (2605–2636),
`_verify_public_surface_regression` (2639–2970).

**`annotation_reconcile.py`** — `_index_function_defs` (2973–2993), `_parse_declared_def`
(2996–3022), `_signature_slots` (3025–3055), `_line_start_byte_offsets` (3058–3065),
`_node_byte_span` (3068–3084), `_apply_byte_edits` (3087–3100), `_annotation_only_edits`
(3103–3163), `_reconcile_declared_annotation_drift` (3166–3236).

**`interface_check.py`** — `_collect_python_symbols` (3540–3576),
`_parse_declared_param_names` (3579–3612), `_collect_actual_param_names` (3615–3628),
`ParamSpec` (3636), `_ast_args_to_specs` (3639–3661), `_parse_declared_param_specs`
(3664–3683), `_collect_actual_param_specs` (3686–3690), `_find_target_function`
(3693–3753), `_extract_pdd_interface_signatures` (3756–3837), `_collect_pdd_interface_names`
(3840–3872), `_verify_pdd_interface_signatures` (3875–4102),
`_verify_architecture_conformance` (4105–4154), `_verify_architecture_json_conformance`
(4157–4302).

**Stays in `code_generator_main.py`** — `console`, `logger`,
`_should_wire_generated_exports`, `_find_prompt_contract_project_root`,
`_run_git_command`, `is_git_repository`, `get_git_content_at_ref`,
`get_file_git_status`, `git_add_files`, `_expand_vars`, `_parse_front_matter`,
`_is_architecture_template`, `_repair_architecture_interface_types`,
`_detect_wireable_exports`, `_wire_to_parent_init`, `code_generator_main`.

### Dependency direction

`code_generator_main` → `pdd.conformance` → `pdd.interface_semantics`.
`pdd.conformance` must not import `code_generator_main`. `sync_orchestration`,
`one_session_sync`, `cmd_test_main`, `agentic_test_generate`, and
`server/routes/prompts.py` import from `pdd.conformance` directly, which is what
removes the two lazy-import workarounds.

## Hazards

These are the parts that will silently undo or corrupt the work if missed.

### H1 — The 38-symbol include selector (highest risk)

`pdd/prompts/code_generator_main_python.prompt:172` self-includes the generated
module by explicit symbol name:

```
<include select="pattern:^ParamSpec\s*=,class:ArchitectureConformanceError,…">
```

38 names, of which the great majority move. If this is not updated in the same
change, the next `pdd sync` regenerates the monolith and silently reverts the
split. This selector was already observed broken earlier in the session with an
`Invalid selector … Class 'LanguageMismatchError' not found in source` comment,
so it is demonstrably fragile.

**Action:** remove every extracted symbol from the selector; point the new
prompts at their own sources.

### H2 — `<pdd-interface>` and `architecture.json` must move with the classes

The orchestrator prompt's `<pdd-interface>` and its `architecture.json` entry both
declare the 5 exception constructors. `_find_target_function` resolves a declared
name to a `ClassDef`/`FunctionDef` in the generated file. Once the classes live in
`pdd/conformance/errors.py`, the orchestrator would declare symbols it no longer
defines and **fail its own conformance check** with
`declares function(s)/method(s) missing from the generated code`.

**Action:** move those 5 declarations to `conformance/errors`'s interface, in both
the prompt and `architecture.json`.

### H3 — Re-exports must use the redundant-alias form

`code_generator_main.py` has no `__all__`. Per the public-surface rules this file
itself implements, a plain `from .conformance.errors import X` is *not* public
surface — so re-exporting that way reads as **symbol removed** and raises
`PublicSurfaceRegressionError`. The redundant alias `import X as X` is the
recognized explicit-re-export form. Even then, the signature entry flips from
`[class]` to `[import:from .conformance.errors]`, which the gate is specified to
diff as a binding-kind change.

**Action:** use `from .conformance.errors import X as X` (or an explicit `__all__`),
and add a one-time `BREAKING-CHANGE: change signature …` line naming the five
classes. `pdd/core/__init__.py` is the working precedent for the `__all__` form.

### H4 — The churn-nonce seam fails *silently*

`tests/test_code_generator_main.py:7446-7449`:

```python
import pdd.code_generator_main as cg
def _fresh():
    cg._CHURN_NONCE_CACHE = None
    cg._CHURN_NONCE_READ = False
```

Direct attribute assignment on the module object, not `patch()`. When these globals
move to `conformance/errors.py`, this keeps setting attributes nothing reads — the
test passes while testing nothing. This is the only seam in the file that fails
quietly rather than loudly.

**Action:** repoint to `pdd.conformance.errors`. Verify by asserting the test fails
when the nonce logic is deliberately broken.

### H5 — Patch call sites

27 `patch("pdd.code_generator_main.X")` call sites exist: `is_git_repository` ×7,
`console` ×6, `get_git_content_at_ref` ×5, `_run_git_command` ×4, `pdd_preprocess` ×2,
`local_code_generator_func` ×2, `code_generator_main` ×1. **All target symbols that
stay in the orchestrator**, so this scope does not disturb them. This is a large part
of why the orchestrator function is out of scope.

Separately, `_collect_patch_targets` only scans *sibling* `test_*.py` files, and
`pdd/` contains none — so the underscore privates are not gate-protected and can
move freely.

### H6 — `TestChurnError` collects as a pytest test class

`TestChurnError` triggers `PytestCollectionWarning` today (pytest tries to collect
it by name prefix, and only skips it because it defines `__init__`). The warning
follows the class to `conformance/errors.py`. Pre-existing, not introduced here;
noted so it is not mistaken for a regression.

## Registration checklist

Per new prompt, mirroring `pdd/core/`:

1. `pdd/prompts/conformance/<name>_python.prompt` with `<pdd-reason>`,
   `<pdd-interface>`, `<pdd-dependency>`.
2. An `architecture.json` entry — `filename: conformance/<name>_python.prompt`,
   `filepath: pdd/conformance/<name>.py` (the `core/…` entries are the template).
3. A `.pddrc` context block mirroring `core:` — without it, paths fall through to
   `pdd_cli` whose `generate_output_path: pdd/` would write to `pdd/<name>.py`
   instead of `pdd/conformance/<name>.py`:

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

4. `context/conformance/<name>_example.py` — a runnable example, per
   `context/core/*_example.py`. **These, not the `pdd/` sources, are what
   `project_dependencies.csv` tracks**: the CSV has 0 rows starting `pdd/` and
   carries `context/core/cli_example.py`, `context/core/errors_example.py`, etc.
   Add a CSV row per example.
5. `pdd/conformance/__init__.py` — hand-written, no prompt, per `pdd/core/__init__.py`.
6. `tests/conformance/test_<name>.py` where warranted.

Coverage of 4–6 is partial in `/core` and need not be exhaustive here: 9 modules,
7 prompts, 6 examples, 3 test files, 1 hand-written `__init__.py`. Examples and
tests are added where they earn their place, not mechanically per module.

### Prompt style

Follow the `/core` prompt form, which differs from today's
`code_generator_main_python.prompt`:

| | `/core` prompts | `code_generator_main_python.prompt` |
|---|---|---|
| YAML front-matter | none | `--- name: … language: Python ---` |
| Section markers | `% Requirements`, `% Deliverables` | `# Requirements`, `# Deliverables` |
| Preamble | `<include>context/python_preamble.prompt</include>` in all 7 | present |
| `<pdd-reason>` / `<pdd-interface>` | both, at top | both |
| `<pdd-dependency>` | only where needed (3 of 7) | 11 declared |
| Closing | `% Deliverables\n  - Code: pdd/core/<name>.py` | numbered deliverables list |

New prompts use the `%` form with no YAML front-matter.

## Verification

Behavior preservation is the acceptance criterion. Because the code is
**regenerated** rather than moved (see "Generation mode"), verification carries
the whole weight of this plan.

### Regeneration discipline

- **One module at a time.** Generate, run the suite, commit. Never sync all nine
  and debug the aggregate.
- **Diff every generated module against the corresponding lines of the current
  monolith** before accepting it. The symbol→module map below gives exact line
  spans for this purpose; a semantic diff of each extracted function against its
  original is the primary drift detector, because the test suite will not catch
  every behavioral nuance in this code.
- **Budget for retries.** `max_attempts: 3` in the `.pddrc` block; if a module
  will not converge, that is a signal the prompt is under-specified, not a reason
  to hand-patch the output.

### Checks

1. **Baseline recorded**: 259 passed, 1 skipped on the focused set
   (`test_issue_67`, `test_issue_67_expansion`, `test_issue_1558_semantic_contracts`,
   `test_issue_1968_annotation_convergence`, `test_prompt_contract_validation`,
   `test_issue_1903_adopt_collocated_test`, `test_issue_686_post_process_args_braces`,
   `test_cmd_test_main`). Must stay green.
2. **Full suite** must be green before merge, including
   `tests/test_code_generator_main.py` (11,888 lines), `test_sync_orchestration.py`,
   `test_agentic_sync_runner.py`, `test_one_session_sync.py`.
3. **Import-surface check**: every symbol previously importable from
   `pdd.code_generator_main` still is, or every consumer is updated. 111 top-level
   symbols inventoried; 30 distinct symbols are imported externally today. Note
   one of the 30 is `requests` — tests do `from pdd.code_generator_main import
   requests` to patch the HTTP client. It stays in the orchestrator.
4. **Gate self-check**: `pdd sync` on `code_generator_main_python.prompt` must pass
   its own architecture-conformance and public-surface gates (H1–H3).
5. **H4 explicitly**: confirm the churn-nonce test still fails when the logic is broken.
6. **No message-format drift**: the string prefixes `Public surface regression for `,
   `Test churn threshold exceeded for `, `Generation output extraction failure for `,
   `Architecture conformance error for `, `Language mismatch for ` are parsed by
   `agentic_sync_runner` across a subprocess boundary and must stay byte-identical.

## Follow-on work

The `pdd split` proposal's remaining children, deferred:
`codegen_generation_phase`, `codegen_postgen_phase` (splitting the orchestrator
function; depends on collaborator injection keeping 17 test-substitution paths
alive), plus finer sub-splits. The tool scored full decomposition at 110 and noted
the shared-layer subset is "the natural first PR if 78 files is too much to land
at once." Re-evaluate against the real diff after this lands.

Also deferred: splitting `tests/test_code_generator_main.py` (11,888 lines; the
proposal estimated 239 of 359 tests move out, leaving 3,500–4,500 lines).

## Related defects

The `pdd split` option-parsing failure encountered while producing this spec is
tracked separately as
[#2372](https://github.com/promptdriven/pdd/issues/2372). Not a blocker for this
work.
