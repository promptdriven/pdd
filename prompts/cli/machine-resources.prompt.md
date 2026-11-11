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
When `ports.includeChecks` is true, add `check:{cpuIds,platform,battery,virtualized,taskset}`.
CPU IDs are the allowed Linux affinity IDs, else available parallelism indices.
Battery detection uses Linux power-supply types. Virtualization is true only after
a successful bounded systemd-detect-virt probe; unknown reserves personal capacity.
Taskset is an executable absolute PATH selection or null. Export
`machineCheckPorts(env, ports)` as the synchronous compatibility adapters for
legacy capacity callers: cores, platform, battery, virtualized, taskset, memory
and load. Its memory adapter returns available bytes by the same platform rule. They use the same native readers; policy stays with the queue.

Ports: `readFile(path)`, `statfs(path)`, `cpuCount()`, `load()`, `memory()`,
`vmStat()` (the `vm_stat` text), `freeMemory()`, `totalMemory()` and `platform`,
with native Node defaults. An injected `memory()` replaces the platform rule. Callers can inject `machineResources`
with the same input/output contract; policy belongs to those callers.

## Dependencies

Node fs and os supply native local observations only. Native tests cover this port.
