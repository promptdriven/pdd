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
  before it can leave.
- The **runner** joins `rb-sandbox` (to receive agent traffic) and
  `rb-proxy-egress` (to forward it). Only the *runner* env carries
  `HTTPS_PROXY=gateway:8888`; the frozen agent env black-holes proxy vars and
  the agent is in a different container anyway.
- The **gateway** ACL (`tinyproxy.conf` + `filter`) refuses CONNECT to
  anything but the pinned provider host on 443, with `Allow` bounded to the
  proxy-egress subnet as defense in depth.

The runner binds the recording proxy to `0.0.0.0` (via
`RunConfig.proxy_host`, set from `RB_PROXY_HOST` in the compose env) so the
agent container can reach it; on a non-container run it stays on loopback.

## Verify (Linux/CI or the pilot machine; no API key, no billing)

```bash
cd research/repo-bloat-benchmark/harness/runner/container
docker compose build
# From the AGENT namespace — the one that must be locked down:
docker compose run --rm agent  python3 harness/runner/container/egress_check.py --role agent
# From the RUNNER namespace — the gateway ACL itself:
docker compose run --rm runner python3 harness/runner/container/egress_check.py --role runner
```

Both must print `EGRESS LOCKDOWN … VERIFIED`. The **agent** role asserts: no
TCP/UDP/IPv6 egress, the gateway is **unreachable** from the agent, the
recording proxy **is** reachable, loopback works. The **runner** role
asserts the gateway grants the pinned provider and refuses every other host.
**Run both before every pilot session** — the container-tier analogue of the
§6.6 calibration gate.

## Status / provenance

Authored and reviewed on macOS where Docker is unavailable. The compose
topology relies only on standard Docker semantics (`internal: true` networks
attach no gateway; a container reaches only networks it joins), and
`egress_check.py` verifies the actual runtime properties **empirically on the
pilot machine** rather than trusting configuration. Until both roles have
printed VERIFIED on a Docker host, treat the tier as *implemented, field
verification pending* — running both checks is mandatory, not optional. The
`Allow` CIDRs and the `runner:8080` proxy port assume Docker's default
address pools; adjust if your daemon differs (the checks will catch a
mismatch).
