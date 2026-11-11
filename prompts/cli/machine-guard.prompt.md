# Machine guard for Autopilot

Own `src/machine-guard.mjs`. It is the small resource governor of the
[Autopilot core](autopilot-core.prompt.md) (#3231): Autopilot never takes over a
person's machine, on any repository, with no setup per repository. Autopilot may use
a **share** of the machine's CPU and memory, for all its repositories together: 50% by
default, or the percent that a person gives with `pdd autopilot start --share PERCENT`
(saved by the [launcher](autopilot-launcher.prompt.md)). The share of the real limits
decides the slots; the room for new work compares what all Autopilot jobs on this
machine use now (every repository) with that share; the priority and the cleanup
limits are fixed.
The guard reads nothing by itself except through the
[machine observations](machine-resources.prompt.md); every function here except
`readMachineGuard` is pure. It makes no GitHub, network or model call. There is no
machine class: the operating system decides nothing, and there is no battery check
(Serhan: "no need to check battery. but cpu and memory make sense. and also by default
we can make 50% and user should be able to configure it when they start how much
percent").

Why: a person ran Autopilot on a laptop, and Autopilot took almost all of its CPU and
memory. On our runner VM, in laptop-sized cgroups, one core agent job used 0.1 to 0.3
GiB and less than one core; the full test suite kept 61-65% of the cores busy with a
memory peak of 2.3-2.8 GiB, and the suite queue already runs one full suite at a time
on a person's machine.

## The numbers

All numbers are in one frozen table, `GUARD`, so they are easy to change. Nothing
else in pdd repeats them.

| Name | Value | Meaning |
|---|---|---|
| `share` | 50 | the default percent of the CPU and memory that Autopilot may use |
| `maxSlots` | 4 | never more jobs at once |
| `jobCores`, `jobBytes` | 2 cores, 3 GiB | one job: an agent (0.1-0.3 GiB, under one core) and its part of one full suite (2.3-2.8 GiB) |
| `diskBytes`, `diskShare` | 10 GiB, 5% | the free disk that new work needs (a job makes up to 3 checkouts and installs dependencies) |
| `pressurePsi` | 10 | Linux PSI `memory some avg10` at or above it is memory pressure; on macOS a pressure level above 1 (normal) is |
| `nice`, `qos` | 19, `utility` | the lowest priority for every Autopilot process |
| `cpuWeight`, `cpuWeightFull` | 1, 100 | the systemd `CPUWeight` below a share of 100, and at 100: a weight counts only when the CPU is contended, so an idle machine still gives Autopilot all of it |
| `logDays`, `logBytes` | 14 days, 500 MiB | the cleanup of old job logs |

Examples at 50% (one test each): an 8 GB, 8-core Mac gets 1 slot; a 32 GB, 10-core
Mac gets 2; pdd-vm (64 cores, 251 GB) gets 4, and with 2 repositories they share those 4;
a 4-CPU, 8 GB Linux container gets 1. At a share of 100 the 32 GB Mac gets 4.

## Public contract

- `validShare(value)` is true for a whole number from 1 to 100; `shareOf(value)` is
  the value when it is valid, else `GUARD.share`.
- `usableCores(resources)` is the number of cores that this process may use: the
  allowed CPU list (`check.cpuIds`), else `cpuCount`, lowered to the cgroup CPU limit
  (`cgroup.cpus`, rounded down, at least 1) when there is one. `memoryLimit(resources)`
  is the total memory, lowered to the cgroup limit (`cgroup.memoryMax`); `freeMemory`
  is the available memory, lowered to the cgroup room (`cgroup.memoryFree`). So a
  container or a limited systemd unit counts its real limits, not only the host
  numbers. Unknown values are null.
- `shareCores(resources, share)` is the share of the usable cores, rounded down, at
  least 1.
- `slotMath(resources, share)` returns `{slots, share, cores, limit, byCores,
  byMemory}`: `byCores` = floor(cores × share ÷ 100 ÷ `jobCores`), `byMemory` =
  floor(memory limit × share ÷ 100 ÷ `jobBytes`), and `slots` = the lower of the two,
  at least 1 and at most `maxSlots`; an unknown value leaves out its term, and with no
  known term `slots` is 1.
  `autoSlots` is its `slots`.
- `slotCount({auto, runs, repoRuns})` returns `{slots, source}`. The machine's own
  `pdd autopilot start --runs N` (`runs`, saved in the launcher state) wins: source
  `this machine, --runs N`. Else the repository's `autopilot.runs` in `pdd.json`
  (`repoRuns`) can only lower `auto` (pdd.json is shared by every machine of a
  repository, so it never raises one): source `pdd.json autopilot.runs`; else
  `automatic`. A `runs` or `repoRuns` that is not a positive safe integer is absent.
- `machineRoom(resources, share, use)` returns `{ok, reason, free}`, the one room check
  before new work, for the whole machine. `use` is what all Autopilot jobs on this
  machine use now, every repository together: `{jobs, rss, cores}` (the slot-holding
  jobs of every repository, and the memory and CPU of every job process tree). `free`
  is `slotMath(...).slots - jobs`, at least 0 (0 with no room): the jobs that the
  machine's share still allows. The reasons, in this order, the first that holds: `J of
  M Autopilot jobs on this machine run (all repositories, P% share)`, `memory cannot be
  read`, `only N GiB of memory free; a job needs 3 GiB`, `Autopilot uses N GiB on this
  machine; a new job would pass its S GiB share (P%)` (use plus one job above the share
  of the memory limit), `memory pressure`, `disk cannot be read`, `only N GiB of disk
  free; a job needs 10 GiB and 5%`, `Autopilot uses N cores on this machine, its P%
  share is C` (use at or above `shareCores`). Unreadable pressure falls back to the
  memory numbers alone; an unknown use is not checked. Numbers in a reason have at most
  one decimal.
- `jobPriority({platform, role, resources, share, taskset})` returns the spec part
  that the [job runner](agent-job.prompt.md) applies, `{nice: 19, qos, cpus, taskset,
  checkCpus}`. `qos` is `utility` on macOS, else null. `cpus` is a CPU list (`0-3` or
  `0,2,4`) of the first `shareCores` allowed CPU ids, only on Linux with an absolute
  `taskset` when the share is fewer CPUs than the list, and only for an agent role
  (every role except `suite`, `vectors` and `runtime`: the suite queue pins suites to
  its own share and would halve it again, and `pdd test` is a waiting client); else
  null. `checkCpus` is `shareCores` for every role: the job's `PDD_CHECK_CPUS`, the
  worker count that the briefs ask agents to pass to tests and builds.
- `timerPriority(platform, share)` returns the timer lines `{plist, unit}`: on macOS
  `plist` is `<key>Nice</key><integer>19</integer>` (launchd); on Linux `unit` is
  `Nice=19\nCPUWeight=W\nMemoryHigh=SHARE%\n` (a systemd service section; SHARE is
  `shareOf(share)`, W is 1 below 100 and 100 at 100). Linux shares CPU between cgroups by weight before nice counts, and
  the detached jobs stay in the service's cgroup after the tick, so these lines cover
  all Autopilot work there. `MemoryHigh` slows Autopilot under memory pressure and
  kills nothing. Other platforms get empty strings.
- `guardLine(guard)` is the status line, local facts only, with the slot math, for
  example `Machine: share 50% (default) of 10 cores and 16 GiB · slots min(4, 5 cores ÷
  2, 8 GiB ÷ 3 GiB) = 2 → 2 (automatic) · Autopilot on this machine now: 1 job, 0.4 GiB,
  0.3 cores · memory 6.1 GiB free, pressure normal · disk 210 GiB free · load 3.2 ·
  priority low · new work: ok`, or `… · new work: held (REASON)`. The share source is `default` or `this machine, --share`. Unknown values
  are `unknown` (in the math `?`).
- `readMachineGuard({cwd, runs, repoRuns, share, jobs}, ports)` reads the machine once
  through `readMachineResources({cwd}, {...ports, includeChecks: true, includeGuard:
  true})` (or `ports.machineResources`) and the use of all Autopilot jobs through
  `readAutopilotUse` (or `ports.autopilotUse`); `jobs` is the slot-holding jobs of every
  repository of this machine (the launcher counts them). It returns `{share,
  shareSource, slots, source, auto, room, resources, use, priority(role), line}`. `priority(role)` is `jobPriority` with
  the machine's facts; `line` is `guardLine`. A failed read gives `auto` 1, the slots
  of `slotCount`, and no room (`machine resources cannot be read`).

## Dependencies

- [Machine observations](machine-resources.prompt.md): required for
  `readMachineResources` with `includeChecks` and `includeGuard` (CPU ids, taskset,
  cgroup limits and memory pressure) and `readAutopilotUse`.
