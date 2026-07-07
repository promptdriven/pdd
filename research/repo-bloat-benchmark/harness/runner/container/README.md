# Kernel-level egress lockdown (design §8.1.1 hard tier)

The env-var egress guard in `env_freeze.py` is the *portable* layer; it
stops proxy-honoring HTTP stacks but is not kernel enforcement. This
directory is the **hard tier**: pilot cells run inside a Docker network
namespace with **no route to the outside world**.

## Topology

```
                 rb-internal (internal: true — Docker attaches NO gateway)
   ┌──────────────────────────────┐
   │ runner: harness + pinned     │        rb-egress (NAT)
   │ codex; agent subprocess      │   ┌─────────────────────┐
   │ shares this netns.           │──▶│ gateway: tinyproxy,  │──▶ api.openai.com:443
   │ RecordingProxy (in-process)  │   │ FilterDefaultDeny,   │     (and nothing else)
   │ forwards via HTTPS_PROXY.    │   │ ConnectPort 443      │
   └──────────────────────────────┘   └─────────────────────┘
```

- The **agent** runs as a subprocess of the runner and therefore inside the
  same no-egress netns: even a client that ignores every proxy variable has
  no route out. The §8.1.1 frozen agent env additionally black-holes proxy
  vars, so the two tiers compose.
- The **runner process** (not the agent) carries `HTTPS_PROXY=gateway:8888`
  so its in-process RecordingProxy can forward captured requests to the
  provider — every byte on the only egress path is recorded first.
- The **gateway ACL** (`tinyproxy.conf` + `filter`) refuses CONNECT to
  anything but the pinned provider host on 443.

## Verify (Linux/CI or the pilot machine; no API key, no billing)

```bash
cd research/repo-bloat-benchmark/harness/runner/container
docker compose build
docker compose run --rm runner python3 harness/runner/container/egress_check.py
```

`egress_check.py` must print `EGRESS LOCKDOWN VERIFIED`: no direct egress at
the kernel level, gateway reachable, CONNECT to the pinned provider allowed,
CONNECT elsewhere refused, loopback intact. **Run it before every pilot
session** — it is the container-tier analogue of the §6.6 calibration gate.

Then, inside the same service, the normal sequence applies (all still
zero-billing except the final calibration request):

```bash
docker compose run --rm runner python3 -m harness.runner.register_env \
    --arm harness/runner/pilot_arm_codex.json --out registered_env.json
docker compose run --rm runner python3 -m harness.runner.preflight \
    --config scenarios/pdd-find-section/preflight.json
# one paid calibration request + GO/NO-GO (see first_run_calibration.py),
# then the pilot cells.
```

## Status / provenance

Authored and reviewed on macOS where Docker is unavailable; the compose
topology (`internal: true` ⇒ no gateway on the benchmark network) is
standard Docker semantics, and `egress_check.py` verifies it **empirically
on the pilot machine** rather than trusting configuration. Until that check
has been run on the pilot machine, treat the tier as *implemented but not
yet field-verified* — the check is mandatory, not optional.
