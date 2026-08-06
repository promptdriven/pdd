# Splitting the `code_generator_main` prompt

Date: 2026-08-06
Branch: `split/prompt-only-from-main` (worktree, based on `main` @ `c443f2f91`)

## Scope

Split `pdd/prompts/code_generator_main_python.prompt` into a set of smaller
prompts, then generate the code from those prompts. The regenerated modules must
behave the same as today's monolith.

That is the whole job. Consumer import updates and test repointing are in scope
only where the split strictly forces them.

## Baseline

Measured on `main` @ `c443f2f91`:

| | |
|---|---|
| `pdd/prompts/code_generator_main_python.prompt` | 213 lines / 71,311 chars (~29k tokens) |
| `pdd/code_generator_main.py` | 5,879 lines |
| Top-level symbols | 109 |
| Symbols imported externally | 28 |
| Typed exceptions | 4 |

This baseline does **not** include the Language Validity Gate work on
`feat/language-validity-gate` (+70 code lines, `LanguageMismatchError`,
`_verify_language_validity`, and an extra `5b.` requirement section). When that
branch merges, its section needs re-splitting into this structure. Requirement
numbering differs between the two branches; all references below use `main`'s.

## Problem

The prompt is 71,311 chars and **70.8% of it is the conformance gate block**:

| Section | Share of prompt |
|---|---|
| **5b. Public-Surface Regression Gate** | **44.7%** |
| **5. Validation & Conformance** | 14.6% |
| **5c. Test-Churn Gate** | 9.2% |
| **5a. Prose/Empty-Output Gate** | 2.2% |
| *gate subtotal* | **70.8%** |
| 3. Execution Strategy | 4.2% |
| 1. Path Orchestration | 0.9% |
| 2. Incremental Generation | 0.6% |
| 6. Integration & Wiring | 0.6% |
| 4. Post-Processing | 0.5% |
| Instructions / Deliverables / Dependencies | 16.9% |

The same imbalance shows in the code: ~3,784 of 5,879 lines are gate logic.

Size alone would not justify surgery — at 5,879 lines this is only the 6th
largest module in `pdd/`, below `checkup_review_loop.py` (10,336),
`agentic_common.py` (10,128), `llm_invoke.py` (7,408),
`sync_determine_operation.py` (7,024) and `agentic_checkup_orchestrator.py`
(6,463), all of which the project has left flat.

The reason to act is that the gate block is a **library other modules consume**,
not orchestration:

| Symbol | Imported by |
|---|---|
| `_verify_public_surface_regression` | `sync_orchestration`, `one_session_sync` |
| `_verify_test_churn`, `_get_test_churn_threshold`, `_prompt_allows_test_churn` | `cmd_test_main`, `agentic_test_generate`, `one_session_sync` |
| `_is_test_output_path`, `_env_flag_enabled` | `agentic_test_generate`, `one_session_sync` |
| `_find_default_test_files` | `server/routes/prompts.py` |
| the 4 typed exceptions | `sync_main`, `sync_orchestration`, `one_session_sync`, `cmd_test_main`, `agentic_test_generate` |

Two consumers work around the resulting cycle with lazy imports:
`pdd/agentic_test_generate.py:109` ("to avoid a circular dependency") and
`pdd/checkup_review_loop.py:8400` ("Lazy imports: code_generator_main pulls in
the heavy generation…").

`pdd split --intent reduce --propose-only` independently diagnosed this as
`split_shared_layer` (confidence 0.75).

## Precedent

`pdd/interface_semantics.py` was extracted from this same file in June 2026,
grew to 1,111 lines, and dropped off its co-change list.

`pdd/core/` is the house pattern and the template here:

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

Prompts of 22–95 lines are the target shape.

## Generation mode: prompt-only

**Prompts are the source of truth; `pdd sync` produces the `.py` files.** No
hand-authoring of generated modules, no verbatim code moves.

This matches the repo norm — of 114 `.pdd/meta/*.json` fingerprints, 113 record a
PDD-driven command (`fix` 31, `test` 28, `regenerate-public` 4, `sync`/`update` 6,
`?` 40) and only `code_generator_main_python` records `manual`.

**Accepted risk, recorded deliberately.** Commit `16a48378c` (on the other branch)
states that `code_generator_main.py` and its prompt "were hand-authored together…
never went through `pdd generate`". Regeneration therefore asks the model to
re-derive intricate AST logic from prose: `__all__` source-order resolution,
reverse-MRO dataclass `__init__` synthesis, byte-offset annotation splicing. The
5b section is 31,877 characters precisely because that logic resists
specification.

Drift, if it occurs, will be quiet rather than loud. Verification is therefore the
load-bearing part of this plan, and per-module regeneration is required.

## Non-goals

- Splitting the `code_generator_main` function itself into pipeline phases. The
  `pdd split` proposal's top option (12 modules, parent → 774 lines) does this;
  it touches 78 files and rewires collaborator injection that keeps 27
  `patch("pdd.code_generator_main.X")` call sites alive. Deferred.
- Splitting `tests/test_code_generator_main.py`.
- Fixing the `pdd split` option-parsing bug — tracked as
  [#2372](https://github.com/promptdriven/pdd/issues/2372).

## Design

### Layout

```
pdd/conformance/
    __init__.py                  hand-written, re-exports the 4 exceptions
    errors.py                    352
    directives.py                152
    test_churn.py                235
    surface.py                   511
    signatures.py                596
    dataclass_signatures.py      456
    declared_surface.py          498
    annotation_reconcile.py      250
    interface_check.py           734
                                -----
                                3,784 moved

pdd/prompts/conformance/         one *_python.prompt per module above
context/conformance/             one *_example.py where warranted
tests/conformance/               one test_*.py where warranted
```

`pdd/code_generator_main.py` retains **2,095 lines** plus added imports — the
orchestrator function (1,474), git helpers, front-matter/var expansion, wiring.

This mirrors `/core` exactly: `pdd/core/` + `pdd/prompts/core/` +
`context/core/` + `tests/core/`, bound by a `core:` block in `.pddrc`.

### Consumer-facing API

Follows `/core`'s actual convention: **direct module imports**, with
`__init__.py` re-exporting only the hottest module's surface.

`pdd/core/__init__.py` re-exports `.cloud` symbols and nothing else; every other
core module is imported by path (`from .core.errors import handle_error`). Even
`cloud` is mostly imported directly — 12 `from .core.cloud import`.

We mirror that: `errors.py` is our `cloud.py` (widest surface, 5 consumers), so
`pdd/conformance/__init__.py` re-exports the 4 typed exceptions with an explicit
`__all__`. Everything else is imported by path.

Trade-off, accepted: direct imports bind consumers to file names, so moving a
symbol between conformance modules later is a breaking change for them. `/core`
has lived with this fine.

### Module contents

Line spans refer to `pdd/code_generator_main.py` on `main` @ `c443f2f91`.

**`errors.py` (352)** — `_LANGUAGE_TEST_FILE_EXTS` (71–83),
`PROSE_OUTPUT_REPAIR_DIRECTIVE` (85–89), `ArchitectureConformanceError` (92–163),
`PublicSurfaceRegressionError` (166–289), `_CHURN_NONCE_ENV` / `_CHURN_NONCE_CACHE` /
`_CHURN_NONCE_READ` (292–294), `_read_churn_nonce` (297–332), `TestChurnError`
(335–394), `ProseOutputError` (397–435).

**`directives.py` (152)** — `_parse_llm_bool` (439–447), `_env_flag_enabled`
(449–454), `_YAML_FRONT_MATTER_RE` (467–470), `_strip_yaml_front_matter` (473–500),
`_prompt_has_breaking_change_marker` (503–506), `_BREAKING_CHANGE_DIRECTIVE_RE`
(513–516), `_DIRECTIVE_SYMBOL_RE` (525–531), `_iter_breaking_change_directives`
(534–554), `_parse_breaking_change_symbols` (557–578),
`_prompt_breaking_change_removed_symbols` (581–602),
`_prompt_breaking_change_signature_symbols` (605–626),
`_prompt_allows_breaking_change` (2403–2405).

**`test_churn.py` (235)** — `_TEST_CHURN_OPT_OUT_RE` (633–644),
`_TEST_CHURN_TARGET_RE` (645), `_TEST_CHURN_BRIDGE_BREAK_RE` (651–654),
`_prompt_allows_test_churn` (657–692), `_is_python_generation` (695–699),
`_is_test_output_path` (702–769), `_get_test_churn_threshold` (3184–3215),
`_compute_test_churn_ratio` (3218–3233), `_calculate_test_churn_ratio` (3236–3238),
`_verify_test_churn` (3241–3277), `_find_default_test_files` (4315–4335).

**`surface.py` (511)** — `_collect_bound_module_names` (772–822),
`_SCOPE_NODE_TYPES` / `_COMPREHENSION_TYPES` (826–831), `_DUNDER_ALL_MUTATOR_METHODS`
(837–840), `_scannable_children` (843–872), `_node_writes_dunder_all` (875–924),
`_subtree_mutates_dunder_all` (927–935), `_clean_dunder_all_literal` (938–962),
`_extract_dunder_all` (965–1024), `_assign_target_matches` (1027–1035),
`_symbol_exists_in_module` (1038–1076), `_effective_patch_targets` (1079–1092),
`_collect_patch_targets` (1095–1099), `_reexport_binding` (1102–1131),
`_snapshot_public_surface` (1134–1306), `_diff_public_surface` (1309–1311),
`_collect_python_public_surface` (2398–2400).

**`signatures.py` (596)** — `_format_python_signature` (1314–1379),
`_python_method_binding_kind` (1382–1431), `_python_property_accessor_role`
(1434–1456), `_resolve_class_node` (1933–1954), `_class_constructor_signature`
(1957–1991), `_patch_target_signature_entry` (1994–2032),
`_snapshot_public_signatures` (2035–2395).

**`dataclass_signatures.py` (456)** — `_is_dataclass_decorator` (1459–1492),
`_dataclass_decorator_is_kw_only` (1495–1514),
`_dataclass_decorator_synthesizes_init` (1517–1552), `_is_kw_only_sentinel`
(1555–1570), `_dataclass_field_call_is_init_false` (1573–1608),
`_collect_dataclass_own_parts` (1611–1672), `_part_field_name` (1675–1688),
`_collect_dataclass_inherited_parts` (1691–1779),
`_synthesize_dataclass_init_signature` (1782–1930).

**`declared_surface.py` (498)** — `_collect_declared_surface` (2408–2451),
`_declared_signature_to_entry` (2454–2517), `_entry_binding_context` (2520–2533),
`_declared_presence_name` (2536–2547), `_declared_patch_targets` (2550–2581),
`_verify_public_surface_regression` (2584–2915).

**`annotation_reconcile.py` (250)** — `_index_function_defs` (2918–2938),
`_parse_declared_def` (2941–2967), `_signature_slots` (2970–3000),
`_line_start_byte_offsets` (3003–3010), `_node_byte_span` (3013–3029),
`_apply_byte_edits` (3032–3045), `_annotation_only_edits` (3048–3108),
`_reconcile_declared_annotation_drift` (3111–3181).

**`interface_check.py` (734)** — `_collect_python_symbols` (3485–3521),
`_parse_declared_param_names` (3524–3557), `_collect_actual_param_names`
(3560–3573), `ParamSpec` (3581), `_ast_args_to_specs` (3584–3606),
`_parse_declared_param_specs` (3609–3628), `_collect_actual_param_specs`
(3631–3635), `_find_target_function` (3638–3698),
`_extract_pdd_interface_signatures` (3701–3782), `_collect_pdd_interface_names`
(3785–3817), `_verify_pdd_interface_signatures` (3820–4047),
`_verify_architecture_conformance` (4050–4099),
`_verify_architecture_json_conformance` (4102–4247).

**Stays in `code_generator_main.py`** — `console` (56), `logger` (57),
`_should_wire_generated_exports` (3279–3290), `_find_prompt_contract_project_root`
(3293–3331), `_run_git_command` (3334–3342), `is_git_repository` (3344–3358),
`_expand_vars` (3361–3377), `_parse_front_matter` (3380–3414),
`_is_architecture_template` (3417–3419), `_repair_architecture_interface_types`
(3422–3482), `get_git_content_at_ref` (4250–4275), `get_file_git_status`
(4277–4288), `git_add_files` (4290–4312), `_detect_wireable_exports` (4338–4354),
`_wire_to_parent_init` (4357–4403), `code_generator_main` (4406–5879).

### Prompt decomposition

Each new prompt takes its requirement text from the corresponding section of the
existing prompt:

| New prompt | Source section | Source chars |
|---|---|---|
| `errors_python.prompt` | 5a + the exception contracts embedded in 5 / 5b / 5c | — |
| `directives_python.prompt` | `BREAKING-CHANGE` parsing inside 5b / 5c | — |
| `test_churn_python.prompt` | 5c | 6,559 |
| `surface` / `signatures` / `dataclass_signatures` / `declared_surface` / `annotation_reconcile` | 5b, subdivided | 31,877 |
| `interface_check_python.prompt` | 5 | 10,445 |

The exception contracts are currently interleaved with the gate logic that raises
them, so `errors_python.prompt` is assembled from fragments rather than lifted
whole. That is the one prompt whose text must be composed rather than moved.

The orchestrator prompt retains sections 1, 2, 3, 4, 6, and the orchestration
parts of Instructions/Deliverables — roughly 29% of today's text — plus
`<pdd-dependency>` lines pointing at the new prompts.

### Dependency direction

`code_generator_main` → `pdd.conformance` → `pdd.interface_semantics`.
`pdd.conformance` must not import `code_generator_main`.

## Hazards

### H1 — The 36-symbol include selector (highest risk)

`pdd/prompts/code_generator_main_python.prompt:168` self-includes the generated
module by explicit symbol name:

```
<include select="pattern:^ParamSpec\s*=,class:ArchitectureConformanceError,…">
```

**36 symbols, of which 25 move and 11 stay.** If this is not updated in the same
change, the next `pdd sync` regenerates the monolith and silently reverts the
split.

Moving: the 4 exception classes; `_verify_architecture_conformance`,
`_verify_architecture_json_conformance`, `_verify_pdd_interface_signatures`,
`_extract_pdd_interface_signatures`, `_parse_declared_param_names`,
`_collect_actual_param_names`, `_parse_declared_param_specs`,
`_collect_actual_param_specs`, `_ast_args_to_specs`, `_find_target_function`,
`_collect_python_symbols`, `pattern:^ParamSpec\s*=`; `_collect_declared_surface`,
`_declared_signature_to_entry`, `_declared_presence_name`,
`_declared_patch_targets`, `_entry_binding_context`;
`_class_constructor_signature`, `_resolve_class_node`,
`_patch_target_signature_entry`; `_symbol_exists_in_module`.

Staying: `code_generator_main`, `_run_discovery` (nested inside it),
`_should_wire_generated_exports`, `_wire_to_parent_init`, `_parse_front_matter`,
`_expand_vars`, `_run_git_command`, `is_git_repository`, `get_git_content_at_ref`,
`get_file_git_status`, `git_add_files`.

### H2 — `<pdd-interface>` and `architecture.json` must move with the classes

The orchestrator prompt's `<pdd-interface>` and its `architecture.json` entry both
declare the 4 exception constructors alongside `is_git_repository`,
`get_git_content_at_ref`, `get_file_git_status`, `git_add_files`, and
`code_generator_main`. `_find_target_function` resolves a declared name to a
`ClassDef`/`FunctionDef` in the generated file. Once the classes live in
`pdd/conformance/errors.py`, the orchestrator would declare symbols it no longer
defines and **fail its own conformance check** with
`declares function(s)/method(s) missing from the generated code`.

**Action:** in both the prompt's `<pdd-interface>` and the `architecture.json`
entry for `code_generator_main_python.prompt`, remove the 4 exception entries;
add a new `architecture.json` entry per conformance prompt carrying its own
interface; and update the orchestrator entry's `dependencies` array to list the
new conformance prompts. The four `core/*_python.prompt` entries are the template
for `filename`/`filepath` shape (`core/errors_python.prompt` → `pdd/core/errors.py`).

### H3 — Re-exports must use the redundant-alias form

`code_generator_main.py` has no `__all__`. Per the public-surface rules this file
itself implements, a plain `from .conformance.errors import X` is *not* public
surface — so re-exporting that way reads as **symbol removed** and raises
`PublicSurfaceRegressionError`. The redundant alias `import X as X` is the
recognized explicit-re-export form. Even then the signature entry flips from
`[class]` to `[import:from .conformance.errors]`, which the gate diffs as a
binding-kind change.

**Action:** use `from .conformance.errors import X as X` (or an explicit
`__all__`), plus a one-time `BREAKING-CHANGE: change signature …` line naming the
four classes. `pdd/core/__init__.py` is the working precedent.

### H4 — The churn-nonce seam fails *silently*

`tests/test_code_generator_main.py` assigns the nonce globals directly rather than
patching:

```python
import pdd.code_generator_main as cg
cg._CHURN_NONCE_CACHE = None
cg._CHURN_NONCE_READ = False
```

When these move to `conformance/errors.py`, this keeps setting attributes nothing
reads — the test passes while testing nothing. The only seam here that fails
quietly rather than loudly.

**Action:** repoint to `pdd.conformance.errors`; verify by confirming the test
fails when the nonce logic is deliberately broken.

### H5 — Patch call sites

27 `patch("pdd.code_generator_main.X")` call sites exist: `is_git_repository` ×7,
`console` ×6, `get_git_content_at_ref` ×5, `_run_git_command` ×4, `pdd_preprocess`
×2, `local_code_generator_func` ×2, `code_generator_main` ×1. **All target symbols
that stay in the orchestrator**, so this scope does not disturb them — a large
part of why the orchestrator function is out of scope.

`_collect_patch_targets` only scans *sibling* `test_*.py` files and `pdd/` has
none, so the underscore privates are not gate-protected and can move freely.

### H6 — `TestChurnError` collects as a pytest test class

`TestChurnError` triggers `PytestCollectionWarning` today (pytest tries to collect
it by name prefix, and only skips it because it defines `__init__`). The warning
follows the class. Pre-existing, not introduced here.

## Registration checklist

Per new prompt, mirroring `/core`:

1. `pdd/prompts/conformance/<name>_python.prompt` with `<pdd-reason>`,
   `<pdd-interface>`, and `<pdd-dependency>` where needed.
2. An `architecture.json` entry — `filename: conformance/<name>_python.prompt`,
   `filepath: pdd/conformance/<name>.py`, with `dependencies`, `priority`, `tags`
   and `interface`.
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

4. `context/conformance/<name>_example.py`. **These, not the `pdd/` sources, are
   what `project_dependencies.csv` tracks** — the CSV has 0 rows starting `pdd/`
   and carries `context/core/cli_example.py` etc. Add a CSV row per example.
5. `pdd/conformance/__init__.py` — hand-written, no prompt.
6. `tests/conformance/test_<name>.py` where warranted.

Coverage of 4–6 is partial in `/core` and need not be exhaustive: 9 modules,
7 prompts, 6 examples, 3 test files, 1 hand-written `__init__.py`.

### Prompt style

Follow the `/core` form, which differs from today's orchestrator prompt:

| | `/core` prompts | `code_generator_main_python.prompt` |
|---|---|---|
| YAML front-matter | none | `--- name: … language: Python ---` |
| Section markers | `% Requirements`, `% Deliverables` | `# Requirements`, `# Deliverables` |
| Preamble | `<include>context/python_preamble.prompt</include>` in all 7 | present |
| `<pdd-reason>` / `<pdd-interface>` | both, at top | both |
| `<pdd-dependency>` | only where needed (3 of 7) | 11 declared |
| Closing | `% Deliverables\n  - Code: pdd/core/<name>.py` | numbered list |

New prompts use the `%` form with no YAML front-matter.

## Verification

Behavior preservation is the acceptance criterion. Because the code is
**regenerated** rather than moved, verification carries the whole weight here.

### Regeneration discipline

- **One module at a time.** Generate, run the suite, commit. Never sync all nine
  and debug the aggregate.
- **Diff every generated module against the corresponding line spans above**
  before accepting it. This is the primary drift detector — the test suite will
  not catch every behavioral nuance in this code.
- **No hand-patching generated output.** A module that will not converge means the
  prompt is under-specified; fix the prompt.
- Order (dependencies first): `errors` → `directives` → `test_churn` → `surface`
  → `dataclass_signatures` → `signatures` → `declared_surface` →
  `annotation_reconcile` → `interface_check` → orchestrator.

### Checks

1. **Baseline**: capture a green run of the focused set before starting
   (`test_issue_67`, `test_issue_67_expansion`, `test_issue_1558_semantic_contracts`,
   `test_issue_1968_annotation_convergence`, `test_prompt_contract_validation`,
   `test_issue_1903_adopt_collocated_test`, `test_issue_686_post_process_args_braces`,
   `test_cmd_test_main`). On `feat/language-validity-gate` this was
   259 passed / 1 skipped; re-measure on `main`.
2. **Full suite** green before merge, including `tests/test_code_generator_main.py`,
   `test_sync_orchestration.py`, `test_agentic_sync_runner.py`,
   `test_one_session_sync.py`.
3. **Import surface**: all 28 externally-imported symbols still importable, or
   every consumer updated. One of the 28 is `requests` — tests do
   `from pdd.code_generator_main import requests` to patch the HTTP client; it
   stays in the orchestrator.
4. **Gate self-check**: `pdd sync` on `code_generator_main_python.prompt` passes
   its own architecture-conformance and public-surface gates (H1–H3).
5. **H4 explicitly**: confirm the churn-nonce test fails when the logic is broken.
6. **No message-format drift**: the prefixes `Public surface regression for `,
   `Test churn threshold exceeded for `, `Generation output extraction failure for `,
   and `Architecture conformance error for ` are parsed by `agentic_sync_runner`
   across a subprocess boundary and must stay byte-identical.

## Follow-on work

- The `pdd split` proposal's remaining children: `codegen_generation_phase`,
  `codegen_postgen_phase` and finer sub-splits. Re-evaluate after this lands.
- Splitting `tests/test_code_generator_main.py`.
- **Language Validity Gate — layers on afterwards, by its author.** PR
  [#2370](https://github.com/promptdriven/pdd/pull/2370) (`feat/language-validity-gate`,
  OPEN, MERGEABLE, +241/−15 across 3 files) adds `LanguageMismatchError`,
  `_verify_language_validity` and a `5b.` requirement section. Decision: this
  split lands first against `main`; #2370 is then re-targeted on top, with
  `LanguageMismatchError` authored into `pdd/prompts/conformance/errors_python.prompt`
  alongside the other four exceptions and `_verify_language_validity` into the
  module that owns it. Note this shifts `main`'s section numbering (its gate is
  inserted as `5b`, pushing public-surface to `5c` and test-churn to `5d`), which
  is why this spec pins every reference to `main` @ `c443f2f91`.

## Related defects

`pdd split` option-parsing failure encountered while producing this spec:
[#2372](https://github.com/promptdriven/pdd/issues/2372). Not a blocker.
