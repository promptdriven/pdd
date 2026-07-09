# Kernel-level egress lockdown (design §8.1.1 hard tier)

The env-var egress guard in `env_freeze.py` is the *portable* layer; it
stops proxy-honoring HTTP stacks but is not kernel enforcement. This
directory is the **hard tier**: the agent runs in a Docker network namespace
with **no route to the outside world and no route to the egress gateway** —
so it cannot fetch external help *and* cannot bypass the recording proxy.

## Why three namespaces (and not one)

An earlier single-network design ran the agent as a subprocess of the runner,
sharing one netns. Because the gateway was reachable on that network, the
agent could have talked to the gateway directly and reached the provider
**without being recorded**. The recording-completeness guarantee then rested
only on the env-var guard, not on the kernel. This topology fixes that: the
agent is a **separate container** whose only network has no gateway on it.

```
   rb-sandbox (internal: true)              rb-proxy-egress (internal: true)      rb-egress (NAT)
 ┌────────────────────────┐               ┌──────────────────────────┐        ┌──────────────┐
 │ agent: pinned codex     │──────────────│ runner: harness +         │────────│ gateway:      │──▶ api.openai.com:443
 │ under §8.1.1 frozen env │  OPENAI_BASE  │ in-process RecordingProxy │ HTTPS_ │ tinyproxy ACL │    (and nothing else)
 │ ONLY reaches the proxy  │  _URL=runner  │ (binds 0.0.0.0)           │ PROXY  │ provider-only │
 └────────────────────────┘               └──────────────────────────┘        └──────────────┘
   no gateway, no egress                    forwards recorded traffic only
```

- The **agent** container joins `rb-sandbox` only. It has **no interface** on
  `rb-proxy-egress`, so it kernel-cannot address the gateway; its single
  reachable peer is the runner's recording proxy
  (`OPENAI_BASE_URL=runner:<port>`). Every provider request is recorded
  before it can leave. Docker unavoidably runs its embedded resolver at
  `127.0.0.11` inside any container on an internal user-defined network — it
  cannot be removed without granting the agent `NET_ADMIN`, which would defeat
  the kernel isolation. The service therefore pins that resolver's upstream to
  a dead loopback (`dns: 127.0.0.1`): `runner` service-name resolution still
  works, but any **external**-name lookup SERVFAILs, so no name can be
  exfiltrated via DNS. The agent egress check enforces exactly that invariant —
  it fails only if `127.0.0.11` actually *resolves* an external name, not
  because the always-present resolver answers at all.
- The **runner** joins `rb-sandbox` (to receive agent traffic) and
  `rb-proxy-egress` (to forward it). Only the *runner* env carries
  `HTTPS_PROXY=gateway:8888`; the frozen agent env black-holes proxy vars and
  the agent is in a different container anyway.
- The **gateway** ACL (`tinyproxy.conf` + `filter`) refuses CONNECT to
  anything but the pinned provider host on 443, with `Allow` bounded to the
  proxy-egress subnet as defense in depth.

The runner binds the recording proxy to `0.0.0.0` (via
`RunConfig.proxy_host`, set from `RB_PROXY_HOST` in the compose env) so the
agent container can reach it, but advertises the routable service host
`runner` (`RunConfig.proxy_advertised_host`, from
`RB_PROXY_ADVERTISED_HOST`) so the frozen agent never receives
`http://0.0.0.0:<port>`. The actual command-arm process is launched inside
the agent container by `harness.runner.container.agent_worker`, which polls
shared launch requests from the runner; the runner itself no longer executes
the agent locally.

## Verify (Linux/CI or the pilot machine; no API key, no billing)

```bash
cd research/repo-bloat-benchmark/harness/runner/container
docker compose build
# Start the isolated agent worker once per session:
docker compose up -d agent
# From the RUNNER namespace — the gateway ACL itself. `--use-aliases` is
# required because the live recording proxy runs in this one-off container and
# the isolated agent resolves it by the stable `runner` service alias.
docker compose run --rm --use-aliases runner python3 harness/runner/container/egress_check.py --role runner
# Zero-billing end-to-end smoke: launch the real command arm inside `agent`,
# run the agent-role egress check against the live `runner:<port>` recording
# proxy endpoint, prove the frozen CODEX_HOME is shared, and confirm the
# gateway stays unreachable:
docker compose run --rm --use-aliases runner python3 -m harness.runner.container.integration_check
```

The **runner** role asserts the gateway grants the pinned provider and
refuses every other host. The integration check then exercises the actual
isolated-agent launch path end-to-end with no billing: the agent container
must pass the same `egress_check --role agent` assertions against the live
recording proxy at its advertised endpoint, must not reach the gateway
directly, must not forward external DNS through Docker's embedded resolver,
and must see the shared frozen-home/report artifacts. **Run both before every
pilot session** — the container-tier analogue of the §6.6 calibration gate.

For the real command path, run:

```bash
docker compose up -d agent
docker compose run --rm --use-aliases runner python3 -m harness.runner.container.integration_check
```

That check stays zero-billing: it uses the same `container_worker` launch path
the pilot uses, verifies the agent can see the frozen `CODEX_HOME`/report
artifacts on the shared volumes, runs the agent-role egress checker from
inside the isolated agent namespace, confirms the advertised proxy endpoint is
live, and proves the agent cannot reach the gateway directly.

## Status / provenance

Authored and reviewed on macOS where Docker is unavailable. The compose
topology relies only on standard Docker semantics (`internal: true` networks
attach no gateway; a container reaches only networks it joins), and
`egress_check.py` verifies the actual runtime properties **empirically on the
pilot machine** rather than trusting configuration. Until both roles have
printed VERIFIED on a Docker host, treat the tier as *implemented, field
verification pending* — running both checks is mandatory, not optional. The
`Allow` CIDRs assume Docker's default address pools; adjust if your daemon
differs (the checks will catch a mismatch).
