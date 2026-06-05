# Prompt checkup quality gate

PDD keeps you in **prompt space** until a prompt source-set is clear, covered,
evidenced, and ready to generate from. Prompt checkup is the built-in quality
gate that runs before code generation or change.

## Manual prompt checkup

Inspect any prompt source-set directly:

```bash
pdd checkup prompts/refund_payment_python.prompt
pdd checkup prompts/
pdd checkup refund_payment
```

These targets run a unified deterministic report that orchestrates existing
engines:

- `pdd checkup lint`
- `pdd checkup contract check`
- `pdd checkup coverage`
- waiver / evidence readiness via `pdd checkup gate`
- snapshot policy when nondeterministic tags exist

Focused subcommands remain unchanged for CI and debugging:

```bash
pdd checkup lint <target>
pdd checkup contract check <target>
pdd checkup coverage <target>
pdd checkup gate <target>
pdd checkup snapshot <target>
pdd checkup drift <devunit>
```

GitHub issue and PR checkup modes are unchanged:

```bash
pdd checkup https://github.com/org/repo/issues/123
pdd checkup --pr https://github.com/org/repo/pull/123
```

## Report schema

Machine-readable output uses `--json` and conforms to
`pdd.prompt_source_set_report.v1`:

- `status`: `pass`, `warn`, or `fail`
- `target`: the CLI target string
- `checks[]`: per-engine status summary
- `findings[]`: deterministic findings with `id`, `source_check`, `severity`,
  `file`, `line`, `message`, `recommended_action`, and `fix_command`
- `actions[]`: suggested next commands
- `deterministic_exit_code`: 0 clean, 1 warnings, 2 errors (or strict warnings)

`--strict` affects deterministic exit codes only. `--explain` prints a
read-only finding summary and never changes the exit code.

## Automatic gate

When PDD creates or modifies `.prompt` files during generate or change, prompt
checkup can run automatically on the touched files only.

Modes:

| Mode | Behavior |
|------|----------|
| `off` | No automatic checkup |
| `warn` (default) | Report issues; do not block downstream work |
| `strict` | Block code generation / change on deterministic failure |

CLI:

```bash
pdd generate ... --prompt-checkup warn
pdd generate ... --prompt-checkup strict
pdd generate ... --no-prompt-checkup

pdd change ... --prompt-checkup warn
pdd change ... --prompt-checkup strict
```

Config (`pyproject.toml`):

```toml
[tool.pdd.checkup]
prompt_gate = "warn"   # off | warn | strict
```

Workflows with no `.prompt` changes are unaffected.

## Related docs

- [checkup_verifier.md](checkup_verifier.md)
- [prompt_lint.md](prompt_lint.md)
- [coverage_contracts.md](coverage_contracts.md)
- [evidence_manifest.md](evidence_manifest.md)
