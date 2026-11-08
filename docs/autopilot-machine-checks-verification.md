# Verify machine-sized Autopilot checks

Use Node.js 22.16 or newer. No package install or live service is required.
Run these focused tests from the repository root:

```sh
env -u CODEX_HOME node --test --test-concurrency=4 test/autopilot-machine-checks.test.mjs test/autopilot-machine-checks.formal.test.mjs test/test-suite-queue.test.mjs test/autopilot-launcher.test.mjs test/autopilot-native-capacity.test.mjs test/vm-suite.test.mjs
```

The tests call the public queue, CLI, launcher and native admission functions.
Machine ports supply synthetic CPU IDs, memory, load, platform, battery,
virtualization and taskset availability. Queue state uses isolated temporary
directories. Program ports capture spawn arguments or use controlled child programs. Cleanup releases
checks and removes their temporary files. Deterministic tests do not read the host
CPU, memory or load. One Linux integration case reads the current allowed CPU IDs
and invokes real taskset, nproc and Node in a temporary queue. It skips when Linux, four allowed CPUs or the tools are
unavailable. No test uses a live agent, GitHub account, timer or Autopilot state folder.

Cases cover 4, 8, 16, 32, 64 and 96 cores, low memory, load at and above the
usable-core boundary, personal machines, hint-only execution, saved overrides,
resize, queue order, paused time, status and current native run admission.
The bounded test covers every core count from 1 through 128 and free-memory
quantity from 0 through 32 GiB, with personal/affinity combinations, slot overrides,
virtualized and physical machines, and both load boundaries. It checks 405504
capacity observations.

The native process cases check command transport, cwd, environment, status,
timeout and descendant cleanup. The injected spawn case checks the taskset CPU
list and env hint. The Linux integration case checks that a desktop child sees
two CPUs from four allowed CPUs in nproc and Node, plus the matching hint and
saved ticket. Actual macOS worker-tool behavior requires a separate platform integration check. Native
tests do not establish a prompt-interpreter verdict or approve prompts.

Regression cases use the `repair 1` name prefix in the machine and launcher
test files. They cover a Linux desktop without a battery, a detected VM,
conservative detection failure, two repositories with different overrides,
resize before refresh, expiry, absent and malformed snapshots, and read-only
status. Run them with:

```sh
env -u CODEX_HOME node --test --test-name-pattern='repair 1' test/autopilot-machine-checks.test.mjs test/autopilot-launcher.test.mjs
```

For the negative control, use a temporary archive of the candidate and replace
only `src/test-suite-queue.mjs` and `src/autopilot-launcher.mjs` with the reviewed
pre-repair versions. Run the same command. All applicable repair cases must fail
with behavior assertions. Remove the temporary source tree after the control.
