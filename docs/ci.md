# CI Tiers

The public repository runs two default GitHub Actions jobs on pull requests:

- `unit-tests`: pytest coverage that excludes tests marked or known to require real LLMs, cloud resources, or private prompts.
- `public-cli-regression`: deterministic CLI regression coverage through `make regression-public`.

`make regression-public` must remain safe for public forks. It must not require API keys, cloud authentication, Infisical, GCP, private repositories, or live LLM calls. Put live model and cloud checks in separate secret-gated workflows or in `pdd_cloud`, not in the default public PR path.

Longer suites remain separate:

- `make regression` and `make sync-regression` exercise LLM-backed CLI flows.
- `make cloud-regression` and cloud batch targets require cloud authentication and should run only in protected or private CI.

Projects with critical modules may add a policy check that rejects unsnapshotted nondeterministic prompt context. The check should fail when a protected prompt uses `<shell>`, `<web>`, or `<include ... query="...">` without a corresponding snapshot-context run artifact. Keep this check separate from public fork-safe regression jobs if it requires private snapshot artifacts or secret-gated web access.

```bash
pdd checkup snapshot prompts/critical_python.prompt
```

The command exits non-zero when active nondeterministic tags are declared but `.pdd/evidence/` contains no replayable snapshot manifest for that prompt.
