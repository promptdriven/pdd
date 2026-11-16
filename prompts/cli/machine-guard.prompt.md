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
| `maxSlots` | 4 | the default automatic slot cap when login pool count is not given |
| `maxLoginSlots`, `slotsPerLogin` | 16, 2 | the automatic slot ceiling when ready Cloud or local logins are given (`2 × readyLogins`, up to 16) |
| `jobCores`, `jobBytes` | 2 cores, 3 GiB | one job: an agent (0.1-0.3 GiB, under one core) and its part of one full suite (2.3-2.8 GiB) |
| `diskBytes`, `diskShare` | 10 GiB, 5% | the free disk that new work needs (a job makes up to 3 checkouts and installs dependencies) |
| `pressurePsi` | 10 | Linux PSI `memory some avg10` at or above it is memory pressure; on macOS a pressure level above 1 (normal) is |
| `nice`, `qos` | 19, `utility` | the lowest priority for every Autopilot process |
| `cpuWeight`, `cpuWeightFull` | 1, 100 | the systemd `CPUWeight` below a share of 100, and at 100: a weight counts only when the CPU is contended, so an idle machine still gives Autopilot all of it |
| `logDays`, `logBytes` | 14 days, 500 MiB | the cleanup of old job logs |

Examples at 50% (one test each): an 8 GB, 8-core Mac gets 1 slot; a 32 GB, 10-core
Mac gets 2; pdd-vm (64 cores, 251 GB) gets 4 by default, scales up to 16 with ready
logins or `--runs N`, and with 2 repositories they share the machine's slots;
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
- `capacityMath(resources, share, {slots, runs, repoRuns, readyLogins})` computes the
  hardware slot ceiling `hardwareSlots` from `byCores`, `byMemory`, and `byDisk`
  (when disk is readable and at or above `max(diskBytes, diskShare × total)`,
  `floor(available ÷ diskBytes)`), at least 1 when any hardware term is known, else
  null. When `runs` is omitted: without `readyLogins`, automatic slots use `maxSlots`
  (4) bounded by `byDisk`; when a safe integer `readyLogins >= 0` is supplied, `0`
  gives `0` automatic slots, and `readyLogins > 0` scales automatic slots up to
  `min(maxLoginSlots, slotsPerLogin × readyLogins, hardwareSlots)`. When `--runs N` is
  set, the effective slot limit is `runs` bounded by `hardwareSlots`, and `limiter`
  records which term bounds admission (`cores`, `memory`, `disk`, `logins`,
  `maxLoginSlots`, `maxSlots`, `repoRuns`, or `runs`).
- `slotCount({auto, runs, repoRuns, hardwareSlots})` returns `{slots, source}` (capped
  by `hardwareSlots` when given). The machine's own `pdd autopilot start --runs N`
  (`runs`, saved in the launcher state) wins: source `this machine, --runs N`. Else
  the repository's `autopilot.runs` in `pdd.json` (`repoRuns`) can only lower `auto`
  (pdd.json is shared by every machine of a repository, so it never raises one):
  source `pdd.json autopilot.runs`; else `automatic` (including `0` when `auto` is
  `0`). A `runs` or `repoRuns` that is not a positive safe integer is absent.
- `machineRoom(resources, share, use, options)` returns `{ok, reason, free}`, the one
  room check before new work, for the whole machine. `options` accepts optional
  `{slots, runs, repoRuns, readyLogins}` so explicit `--runs N` above 4 and
  login-scaled capacity are honored up to `hardwareSlots`. `use` is what all Autopilot
  jobs on this machine use now, every repository together: `{jobs, rss, cores}`.
  `free` is `effectiveSlots - jobs`, at least 0 (0 with no room). The reasons, in this
  order, the first that holds: `no ready Cloud or local logins` (when `readyLogins ===
  0`), `J of M Autopilot jobs on this machine run (all repositories, P% share)` (adding
  `; SOURCE limited by LIMITER` when `--runs` was clamped by hardware), `memory cannot
  be read`, `only N GiB of memory free; a job needs 3 GiB`, `Autopilot uses N GiB on
  this machine; a new job would pass its S GiB share (P%)`, `memory pressure`, `disk
  cannot be read`, `only N GiB of disk free; a job needs 10 GiB and 5%`, `Autopilot
  uses N cores on this machine, its P% share is C`. Unreadable pressure falls back to
  the memory numbers alone; an unknown use is not checked. Numbers in a reason have at
  most one decimal.
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
  `shareOf(share)`, W is 1 below 100 and 100 at 100). Other platforms get empty strings.
- `guardLine(guard)` is the status line, local facts only, with the slot math, the
  effective slot limit, and the limiting term when scaled by logins, raised above 4,
  or clamped by hardware, ending in `new work: ok` or `new work: held (REASON)`.
  The share source is `default` or `this machine, --share`. Unknown values are
  `unknown` (in the math `?`).
- `readMachineGuard({cwd, runs, repoRuns, share, jobs, readyLogins}, ports)` reads the
  machine once through `readMachineResources({cwd}, {...ports, includeChecks: true,
  includeGuard: true})` (or `ports.machineResources`) and the use of all Autopilot
  jobs through `readAutopilotUse` (or `ports.autopilotUse`). It returns `{share,
  shareSource, slots, requestedSlots, hardwareSlots, limiter, limiterDetail, source,
  auto, readyLogins, room, resources, use, priority(role), line}`. A failed read gives
  `auto` 1 (or 0 when `readyLogins === 0`), the slots of `slotCount`, and no room
  (`machine resources cannot be read`).

## Dependencies

- [Machine observations](machine-resources.prompt.md): required for
  `readMachineResources` with `includeChecks` and `includeGuard` (CPU ids, taskset,
  cgroup limits and memory pressure) and `readAutopilotUse`.
