# Architecture Completeness Gate

PDD enforces a complete, deterministic bijection between prompt files, `architecture.json` entries, code artifacts, tests, examples, and fingerprints via a read-only pytest gate.

## Gate location

`tests/test_architecture_completeness.py` — a standard pytest module. No LLM credentials or cloud access required. Runs in the `unit-tests` CI job alongside `pdd checkup --validate-arch-includes`.

## What it checks

The gate enumerates six inventory sources and reports eight failure categories:

| Category | Meaning |
|---|---|
| `PROMPT_WITHOUT_ARCH` | Prompt file on disk with no `architecture.json` entry |
| `ARCH_WITHOUT_PROMPT` | `architecture.json` entry whose prompt file does not exist on disk |
| `PROMPT_WITHOUT_CODE` | Prompt exists but no corresponding code artifact found |
| `CODE_WITHOUT_PROMPT` | Code artifact in architecture but no prompt file |
| `MISSING_TESTS` | Prompt–code pair exists but `tests/test_<stem>.py` is absent |
| `MISSING_EXAMPLES` | Prompt–code pair exists but no example file or directory found |
| `UNRESOLVABLE_ARCH_PATH` | `architecture.json` entry references a path that does not exist |
| `DUPLICATE_ARCH_ENTRY` | Delegated to `tests/test_architecture.py` (not duplicated here) |

Each category is reported separately. Failures name the affected paths so triage is direct.

## Inventory sources

| Source | Discovery path |
|---|---|
| Prompts | `prompts/*_{language}.prompt` (all languages via `LanguageRegistry`) |
| Architecture | All `architecture.json` files via `architecture_registry.find_architecture_for_project` |
| Code | `pdd/*.py`, `pdd/**/*.py` (stem maps to prompt stem minus language suffix) |
| Tests | `tests/test_{stem}.py` |
| Examples | `examples/{stem}/` or `examples/{stem}.py` |
| Fingerprints | `.pdd/meta/{stem}_{language}.json` |

Full relative paths (not bare stems) are used as bijection keys so nested sub-project modules are not aliased against top-level modules with the same basename.

## Mode control: `PDD_ARCH_COMPLETENESS_MODE`

| Value | Behavior |
|---|---|
| `shadow` (default) | Collects and prints all gaps; exits 0. Use during baseline audit. |
| `required` | Exits 1 on any unwaived gap. Use in CI after baseline is resolved. |

```bash
# Local triage (shadow, shows gaps without failing)
pytest tests/test_architecture_completeness.py

# CI strict enforcement (required)
PDD_ARCH_COMPLETENESS_MODE=required pytest tests/test_architecture_completeness.py
```

## Base/head union: deletion-evasion protection

Set `PDD_BASE_REF` and `PDD_HEAD_REF` in CI to enable base/head union. The gate enumerates both refs and unions the inventories: a module present in the base but deleted in the PR branch still appears as a gap. This prevents the "delete the prompt, architecture row, and fingerprint together" evasion path.

The CI workflow sets these variables automatically. Local runs omit them and evaluate only the working tree.

## Waiver file: `.pdd/arch-waivers.json`

Genuinely human-owned or promptless modules require a reasoned, reviewable exception. Add entries to `.pdd/arch-waivers.json` (tracked in git, not gitignored). Schema:

```json
{
  "schema_version": "1",
  "waivers": [
    {
      "waiver_id": "W-construct-paths-001",
      "module_stem": "construct_paths",
      "owner_class": "human_owned",
      "reason": "Hand-written path utility; no prompt planned until seams are added (tracked in #NNN).",
      "approved_by": "github-handle",
      "expires_at": "2027-01-01"
    }
  ]
}
```

Field constraints:
- `owner_class`: `human_owned` or `promptless_utility` — no anonymous exceptions.
- `reason`: non-empty string explaining why the gap is intentional.
- `approved_by`: GitHub handle of the reviewer who signed off.
- `expires_at`: ISO-8601 date — open-ended waivers are not allowed.

The waiver loader uses a base/head union (modeled on `pdd/sync_core/waivers.py:load_sync_waivers`): removing a waiver entry to make a gap disappear is also detected.

**This file is distinct from `docs/architecture_postcheck_waivers.md`**, which records legacy filepath warnings from issue #33.

## Resolving gaps

For each reported gap, choose one of:

1. **Register the module**: Add the missing `architecture.json` entry so global sync can manage it. This is the correct resolution for PDD-owned modules like `construct_paths` or `provider_manager`.
2. **Waive it**: Add an entry to `.pdd/arch-waivers.json` with `owner_class`, `reason`, `approved_by`, and `expires_at`. This is the correct resolution for hand-written CLI glue, `__main__.py`, or other genuinely promptless modules.

The 27–29 top-level gaps identified in the 2026-07-15 audit (including `construct_paths`, `provider_manager`, `one_session_sync`, `config_resolution`, `cli_theme`, `load_prompt_template`) must each be resolved or waived before CI switches to `required` mode.

## Relationship to `pdd checkup --validate-arch-includes`

| Gate | Scope |
|---|---|
| `pdd checkup --validate-arch-includes` | Validates `<include>` / `<pdd-dependency>` tag drift *within* already-registered modules |
| Architecture completeness gate | Catches modules *absent from the registry entirely* and missing artifacts |

Run both in CI. They are complementary: the include-validation gate checks edge consistency; the completeness gate checks vertex completeness.

## Installed-wheel and source-checkout parity

The gate uses `importlib.resources` to enumerate prompts and fingerprints so that it passes whether running from a source checkout or an installed wheel. Missing-path failures distinguish "path not found on disk" from "path not in `architecture.json`".
