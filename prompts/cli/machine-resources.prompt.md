# Machine resource observations

Own `src/machine-resources.mjs`. Export async `readMachineResources({cwd}, ports={})`.
This is the single machine observation port for health and machine-sized check
slots (#3067). It reads no credentials and makes no network or model call.
Return `{cpuCount, load, memory:{available,total}, pressure:{io,memory}, disk:{available,total}}`.
CPU count is a positive integer; load is the one-minute OS load. Memory and disk
quantities are bytes; pressure numbers are Linux PSI `some avg10` percentages.
Use Linux MemAvailable and MemTotal (convert KiB to bytes). On macOS, available
memory is (free + inactive + purgeable pages) times the page size from one
`vm_stat` read, and total is OS total memory: macOS keeps reclaimable pages out of
OS free memory, so free memory alone reads near zero on a healthy Mac and pauses
Autopilot. A failed or malformed `vm_stat` read (no page size, a missing count)
falls back to OS free memory. Other platforms use OS free/total memory. Non-Linux pressure is null for each metric. Use statfs on cwd's volume,
with bavail (space available to this user) and blocks times bsize. Failed or
malformed individual observations return null for that metric; never fabricate a
healthy value. An unreadable pressure file does not hide other observations.
When `ports.includeGuard` is true, add the facts of the
[machine guard](machine-guard.prompt.md) (#3231): `pressure.level` (the macOS `sysctl
-n kern.memorystatus_vm_pressure_level` number, 1 normal, 2 warn, 4 critical; null
elsewhere or when unreadable) and `cgroup:{cpus, memoryMax, memoryFree}`. `cgroup` is
Linux cgroup v2 only, from the process's own cgroup (`/proc/self/cgroup` line
`0::PATH`) and each parent up to `/sys/fs/cgroup`: `cpus` is the lowest `cpu.max`
quota divided by its period (null when every level says `max`); `memoryMax` is the
lowest `memory.max` or `memory.high` of all levels, and `memoryFree` the lowest room
`min(memory.max, memory.high) - memory.current` of a level that has a limit, at least
0 (each null when no level has a limit). Elsewhere `cgroup` is `{cpus: null,
memoryMax: null, memoryFree: null}`. Each read is bounded (a 2 s spawn timeout) and a
failed read is null.
Export `readAutopilotUse(ports)` for the machine guard: one process table read (`ps -A
-o pid=,ppid=,rss=,pcpu=,command=`, `ports.spawnSync`, 5 s timeout) and the sum over
every Autopilot job on this machine, of any repository: each process whose command has
`agent-job.mjs --wrapper` and all its descendants by parent pid, each counted once. It
returns `{processes, wrappers, rss, cores}` (rss in bytes from KiB; cores = %CPU ÷ 100,
two decimals), or null when the table cannot be read.
When `ports.includeChecks` is true, add `check:{cpuIds,platform,battery,virtualized,taskset}`.
CPU IDs are the allowed Linux affinity IDs, else available parallelism indices.
Battery detection uses Linux power-supply types. Virtualization is true only after
a successful bounded systemd-detect-virt probe; unknown reserves personal capacity.
Taskset is an executable absolute PATH selection or null. Export
`machineCheckPorts(env, ports)` as the synchronous compatibility adapters for
legacy capacity callers: cores, platform, battery, virtualized, taskset, memory
and load. Its memory adapter returns available bytes by the same platform rule. They use the same native readers; policy stays with the queue.

Ports: `readFile(path)`, `statfs(path)`, `cpuCount()`, `load()`, `memory()`,
`vmStat()` (the `vm_stat` text), `sysctl(name)`
(the `sysctl -n` text), `freeMemory()`, `totalMemory()` and `platform`,
with native Node defaults. An injected `memory()` replaces the platform rule. Callers can inject `machineResources`
with the same input/output contract; policy belongs to those callers.

## Dependencies

Node fs and os supply native local observations only. Native tests cover this port.
