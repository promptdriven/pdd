# Verify machine-sized Autopilot checks

Use Node.js 22.16 or newer. No package install or live service is required.
Run these focused tests from the repository root:

```sh
env -u CODEX_HOME node --test --test-concurrency=4 test/autopilot-machine-checks.test.mjs test/autopilot-machine-checks.formal.test.mjs test/test-suite-queue.test.mjs test/autopilot-launcher.test.mjs test/autopilot-native-capacity.test.mjs test/vm-suite.test.mjs
```

The tests call the public queue, CLI, launcher and native admission functions.
Machine ports supply synthetic CPU IDs, memory, load, platform, battery and
taskset availability. Queue state uses isolated temporary directories. Program
ports capture spawn arguments or use controlled child programs. Cleanup releases
checks and removes their temporary files. No test reads the machine's CPU, memory
or load, or uses a live agent, GitHub account, timer or Autopilot state folder.

Cases cover 4, 8, 16, 32, 64 and 96 cores, low memory, load at and above the
usable-core boundary, personal machines, hint-only execution, saved overrides,
resize, queue order, paused time, status and current native run admission.
The bounded test covers every core count from 1 through 128 and free-memory
quantity from 0 through 32 GiB, with personal/affinity combinations, slot overrides
and both load boundaries. It checks 202752 capacity observations.

The native process cases check command transport, cwd, environment, status,
timeout and descendant cleanup. The injected spawn case checks the taskset CPU
list and env hint. Actual kernel affinity on Linux and actual macOS worker-tool
behavior require a separate platform integration check. Native tests do not
establish a prompt-interpreter verdict or approve prompts.
