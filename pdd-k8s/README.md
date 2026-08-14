# pdd-k8s

Opt-in local service orchestration for PDD projects.

**Dev Units are not pods.** A Dev Unit is an implementation unit — a prompt and
the code generated from it. A *service* is something you can actually run, and
it is created only when a developer explicitly maps one or more Dev Units onto
it. That distinction is the whole point of this package: PDD stays useful for
scripts, CLIs, libraries and single-process apps, none of which should suddenly
need containers or Kubernetes.

```
Dev Units: router, parser, analyzer
                 │
                 └── "api" service definition
                            │
                     Docker image + port + health check
                            │
                        local Kubernetes pod(s)
```

## Install

```bash
pip install pdd-k8s
pdd-k8s init
```

`init` writes `.pdd/deployments.yaml`. Projects without that file are entirely
unaffected — core PDD never imports this package.

## Manifest

```yaml
version: 1

cluster:
  name: pdd-local
  namespace: pdd-local

services:
  api:
    dev_units: [router, parser, analyzer]
    dockerfile: deploy/Dockerfile
    context: .
    port: 8000
    replicas: 1
    health:
      path: /health
```

**PDD never writes a Dockerfile.** It detects the one you point it at and tells
you what is missing. Auto-generating containers means guessing at build steps,
secrets, databases and runtime commands.

## Commands

| Command | Purpose |
|---|---|
| `pdd-k8s doctor` | Check Docker, kind, kubectl, the manifest, and each service |
| `pdd-k8s services` | List services and the Dev Units they carry |
| `pdd-k8s up [SERVICE...]` | Build → load into the cluster → apply → wait for readiness |
| `pdd-k8s status` | Deploy state, pod readiness, restarts, failure events |
| `pdd-k8s logs SERVICE` | Tail aggregated logs |
| `pdd-k8s down [SERVICE...]` | Remove services (`--cluster` also deletes the cluster) |
| `pdd-k8s manifest` | Print generated Kubernetes YAML without applying it |

Run `doctor` first — it reports missing tooling up front, so failures read as
"Docker is not running" rather than an opaque Kubernetes error later.

## Safety properties

- Every `kubectl` call is pinned to the manifest's own context (`kind-<name>`),
  so an unrelated cluster cannot be touched.
- Only objects labelled `app.kubernetes.io/managed-by=pdd` are ever deleted.
- Images are side-loaded into kind and tagged `:local`; nothing is pushed to a
  registry, and `imagePullPolicy: IfNotPresent` keeps it that way.
- `down` leaves the cluster running unless `--cluster` is passed explicitly.

## No Helm, for now

Plain generated manifests are easier to inspect, diff and trust. Helm becomes
worthwhile later for environment variants, dependencies like Postgres/Redis,
release history and chart publishing.

## Connect integration

`pdd_k8s.api` is the stable facade PDD Connect imports. Every function takes a
project root, returns JSON-serialisable data, and never raises — callers render
whatever `message` comes back. The CLI can evolve independently of it.

## Development

```bash
pip install -e ".[dev]"
pytest
```

The suite fakes every external command, so it needs no Docker, kind or cluster.
