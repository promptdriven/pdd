# `pdd checkup coach --interactive --apply`

Human-approved, deterministic apply for prompt coaching suggestions. Modifies
only `.prompt` and `user_stories/story__*.md` files — never generated code or
policy-review targets.

**Requires `--interactive` and `--apply` together in v1.** The LLM never writes
files directly; every patch is reviewed by the human operator before writing.

## Requirements

- Depends on `pdd checkup coach` (issue #1380), which generates the coaching
  suggestions this command applies.
- A TTY: non-TTY contexts produce an error; no silent writes.

## Usage

```bash
# Review and selectively apply coaching suggestions
pdd checkup coach --interactive --apply

# Preview patches without writing (diff only)
pdd checkup coach --interactive --apply --dry-run

# Apply and re-run contract check --strict on touched prompts
pdd checkup coach --interactive --apply --verify-strict

# Vocabulary-only patches from lint suggestions
pdd checkup lint --interactive --apply TARGET
```

**`--interactive` and `--apply` are both required** to write any file. Passing
`--apply` without `--interactive` produces a clear error. Non-TTY environments
always produce an error.

## Interactive UX

Per patch the operator is prompted:

```
[y]es / [n]o / [e]dit / [s]kip remaining (default: n)
```

- **y** — accept and queue the patch
- **n** (default) — skip this patch
- **e** — open the patch draft in `$EDITOR` before accepting
- **s** — skip this patch and all remaining patches

## Patch kinds

| Kind | Target section | What it does |
|------|----------------|--------------|
| `vocabulary_line` | `<vocabulary>` | Appends a term definition |
| `vocabulary_section_create` | (none yet) | Creates a `<vocabulary>` block |
| `coverage_line` | `<coverage>` | Appends a rule-to-evidence mapping |
| `contract_rule_line` | `<contract_rules>` | Appends a new contract rule |
| `waiver_entry` | `<waivers>` | Appends a waiver block (optional) |
| `story_create` | New file | Creates a `user_stories/story__*.md` file |
| `story_covers_append` | Story `## Covers` | Appends rule references to an existing story |

Patches are applied inside the correct XML section tags via section-aware edits
(`contract_ir`). If a required section tag is absent, the patch fails with a
deterministic error and is skipped unless `--force-apply` is set.

## Flags

| Flag | Description |
|------|-------------|
| `--interactive` | Enable human review; required with `--apply` |
| `--apply` | Write approved patches; required with `--interactive` |
| `--dry-run` | Show diff only; leaves file bytes unchanged |
| `--force-apply` | Apply even when deterministic validation errors exist |
| `--verify-strict` | Re-run `contract check --strict` on touched prompts after apply |
| `--force-overwrite-story` | Allow `story_create` to overwrite an existing file (default: error) |

## Apply log and backups

Every apply run writes:

- **Backup**: `.pdd/evidence/checkups/backups/<run_id>/<original_filename>`
- **Apply log**: `.pdd/evidence/checkups/apply-<run_id>.json` (schema: `pdd.checkup_apply.v1`)

## Safety constraints

- `--dry-run` leaves file bytes unchanged.
- `story_create` fails if the target file already exists; use `--force-overwrite-story` to override.
- Deterministic errors (section not found, path traversal, malformed prompt) block apply unless `--force-apply`.
- No writes to `src/`, generated `pdd/` modules, or policy-check targets.
- No auto-apply by confidence score — human approval is always required.
- No rule line replace-in-place in v1 (append only).
- No CI / non-interactive apply.

## Postflight

After applying patches, the module re-runs `pdd checkup contract check` on every
touched prompt and prints suggested next steps (`coverage`, `sync --evidence`,
`gate`). With `--verify-strict` the postflight exit code propagates to the
command exit code.

## Related

- `pdd checkup coach` — generates the coaching suggestions this command applies (issue #1380).
- `pdd checkup lint --interactive --apply` — vocabulary-only apply from lint suggestions.
- [docs/contract_check.md](contract_check.md) — contract section lint and waiver gate.
- [docs/coverage_contracts.md](coverage_contracts.md) — rule-to-evidence coverage matrix.
