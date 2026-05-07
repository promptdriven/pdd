# CI Tiers

The public repository runs two default GitHub Actions jobs on pull requests:

- `unit-tests`: pytest coverage that excludes tests marked or known to require real LLMs, cloud resources, or private prompts.
- `public-cli-regression`: deterministic CLI regression coverage through `make regression-public`.

`make regression-public` must remain safe for public forks. It must not require API keys, cloud authentication, Infisical, GCP, private repositories, or live LLM calls. Put live model and cloud checks in separate secret-gated workflows or in `pdd_cloud`, not in the default public PR path.

Longer suites remain separate:

- `make regression` and `make sync-regression` exercise LLM-backed CLI flows.
- `make cloud-regression` and cloud batch targets require cloud authentication and should run only in protected or private CI.
