# Machine guard for Autopilot

Own `src/machine-guard.mjs`. It is the small resource governor of the
[Autopilot core](autopilot-core.prompt.md) (#3231): Autopilot never takes over a
person's machine, on any repository, with no setup per repository. It decides the
machine class, the slot count, the room for new work, the process priority and the
cleanup limits from the machine itself. It reads nothing by itself except through
the [machine observations](machine-resources.prompt.md); every function here except
`readMachineGuard` is pure. It makes no GitHub, network or model call.

Why: a person ran Autopilot on a laptop, and Autopilot took almost all of its CPU and
memory. On our runner VM, in laptop-sized cgroups, one core agent job used 0.1 to 0.3
GiB and less than one core; the full test suite kept 61-65% of the cores busy with a
memory peak of 2.3-2.8 GiB. Beside a suite a person kept 81% of their speed; with a
low CPU weight for Autopilot, 99%.

## The numbers

All numbers are in one frozen table, `GUARD`, so they are easy to change. Nothing
else in pdd repeats them.

| Rule | laptop | server |
|---|---|---|
| Slots (automatic) | 1 | min(4, cores ÷ 2, free memory ÷ 3 GiB), at least 1 |
| Room: memory | at least 2 GiB and 15% of the memory free, and no memory pressure | at least 10% free |
| Room: disk | at least 10 GiB and 5% free (a job makes up to 3 checkouts and installs dependencies) | at least 1 GiB and 5% free |
| Room: load | the 1-minute load is not above Autopilot's CPU share | not checked |
| Room: power | on AC power | not checked |
| Autopilot's CPU share | half the cores (at least 1) | all cores |
| Priority | nice 19; macOS utility QoS; systemd `Nice=19`, `CPUWeight=20`, `MemoryHigh=50%` | nice 19; systemd `Nice=19`, `CPUWeight=20` |
| Cleanup | job logs older than 14 days, and the oldest logs while the folder is over 500 MiB; worktrees that no job names | the same |

`GUARD` is `{laptop: {slots: 1, memoryBytes, memoryShare: 0.15, diskBytes, diskShare:
0.05, cpuShare: 0.5, checkLoad: true, checkPower: true, memoryHigh: '50%'}, server:
{maxSlots: 4, coresPerSlot: 2, bytesPerSlot, memoryShare: 0.10, diskBytes, diskShare:
0.05, cpuShare: 1, checkLoad: false, checkPower: false, memoryHigh: null}, nice: 19,
cpuWeight: 20, qos: 'utility', logDays: 14, logBytes}` with the byte values of the
table. Memory pressure is macOS `kern.memorystatus_vm_pressure_level` above 1 (1 is
normal) or Linux PSI `memory some avg10` of 10 or more.

## Public contract

- `machineClass({platform, battery, virtualized})` returns `laptop` for macOS, for
  Linux with a battery and for Linux that is not a virtual machine (the personal
  rule of the [suite queue](test-suite-queue.prompt.md); unknown virtualization
  counts as not virtual), else `server`. A desktop
  Mac is a laptop: it is a person's machine. A machine that only runs Autopilot sets
  its slots with `pdd autopilot start --runs N`.
- `usableCores(resources, klass)` is the number of cores that this process may use:
  the allowed CPU list (`check.cpuIds`), lowered to the cgroup CPU limit
  (`cgroup.cpus`, rounded down, at least 1) when there is one, else `cpuCount`.
  `freeMemory(resources)` is the available memory, lowered to the cgroup room
  (`cgroup.memory`) when there is one. So a container or a limited systemd unit
  counts its real limits, not only the host numbers. Unknown values are null.
- `cpuShare(resources, klass)` is Autopilot's CPU share in cores: `usableCores` times
  the class `cpuShare`, rounded down, at least 1.
- `autoSlots(resources, klass)`: laptop 1; server `min(maxSlots, floor(cores ÷
  coresPerSlot), floor(free memory ÷ bytesPerSlot))`, at least 1; an unknown
  core or memory value leaves out its term.
- `slotCount({klass, auto, runs, repoRuns})` returns `{slots, source}`. The machine's
  own `pdd autopilot start --runs N` (`runs`, saved in the launcher state) wins:
  source `this machine (--runs N)`. Else a server takes the lower of `auto` and the
  repository's `autopilot.runs` in `pdd.json` (`repoRuns`), so a repository can lower
  a server but never raise it above its real room: source `automatic` or
  `pdd.json autopilot.runs`. A laptop ignores `repoRuns` (pdd.json is shared by every
  machine of a repository, so it never raises a person's machine): source
  `automatic`. A `runs` or `repoRuns` that is not a positive safe integer is absent.
- `machineRoom(resources, klass)` returns `{ok, reason}`, the one room check before
  new work. The reasons, in this order, the first that holds: `on battery power`,
  `memory cannot be read`, `only N GiB of memory free (needs M GiB and P%)`, `memory
  pressure`, `disk cannot be read`, `only N GiB of disk free (needs M GiB and P%)`,
  `load L is above Autopilot's share of S cores`. A server checks only memory (its
  share) and disk. Unreadable power counts as AC power; an unreadable pressure falls
  back to the memory numbers alone; an unreadable load is not checked. Numbers in a
  reason have at most one decimal.
- `jobPriority({klass, platform, role, resources, taskset})` returns the spec part
  that the [job runner](agent-job.prompt.md) applies: `{nice: 19, qos, cpus, taskset,
  checkCpus}`. `qos` is `utility` on macOS, else null. `cpus` is a CPU list (`0-3` or
  `0,2,4`) of the first `cpuShare` allowed CPU ids only on a Linux laptop with an
  absolute `taskset`, and only for an agent role (every role except `suite`,
  `vectors` and `runtime`: the suite queue pins suites to its own share and would
  halve it again, and `pdd test` is a waiting client); else null. `checkCpus` is
  `cpuShare` for every role: the job's `PDD_CHECK_CPUS`, the worker count that the
  briefs ask agents to pass to tests and builds.
- `timerPriority(klass, platform)` returns the timer lines: `{plist, unit}`.
  `plist` is `<key>Nice</key><integer>19</integer>` (launchd); `unit` is
  `Nice=19\nCPUWeight=20\n` and, on a laptop, `MemoryHigh=50%\n` (a systemd service
  section). Linux shares CPU between cgroups by weight before nice counts, and the
  detached jobs stay in the service's cgroup after the tick, so one line covers all
  Autopilot work there. `MemoryHigh` slows Autopilot under memory pressure and kills
  nothing.
- `guardLine(guard)` is the status line, local facts only:
  `Machine: laptop · 10 cores, Autopilot uses 5 · memory 3.1 of 16 GiB free, pressure
  normal · disk 210 GiB free · load 7.2 · AC power · priority low · 1 slot (automatic)
  · new work: ok` or `… · new work: held (on battery power)`. Unknown values are
  `unknown`; unknown power reads `power unknown (counts as AC)`.
- `readMachineGuard({cwd, runs, repoRuns}, ports)` reads the machine once through
  `readMachineResources({cwd}, {...ports, includeChecks: true, includeGuard: true})`
  (or `ports.machineResources`) and returns `{klass, slots, source, auto, room,
  resources, priority(role), line}`. `priority(role)` is `jobPriority` with the
  machine's facts; `line` is `guardLine`. A failed read gives the class from
  `ports.platform`, no room (`machine resources cannot be read`) and the slots of
  `slotCount` with `auto` 1.

## Dependencies

- [Machine observations](machine-resources.prompt.md): required for
  `readMachineResources` with `includeChecks` and `includeGuard` (CPU ids, battery,
  virtualization, taskset, cgroup limits, power and memory pressure).
