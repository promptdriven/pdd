# Machine resource observations

Own `src/machine-resources.mjs`. Export async `readMachineResources({cwd}, ports={})`.
This is the single machine observation port for health and machine-sized check
slots (#3067). It reads no credentials and makes no network or model call.
Return `{cpuCount, load, memory:{available,total}, pressure:{io,memory}, disk:{available,total}}`.
CPU count is a positive integer; load is the one-minute OS load. Memory and disk
quantities are bytes; pressure numbers are Linux PSI `some avg10` percentages.
Use Linux MemAvailable and MemTotal (convert KiB to bytes), else OS free/total
memory. Non-Linux pressure is null for each metric. Use statfs on cwd's volume,
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
and load. They use the same native readers; policy stays with the queue.

Ports: `readFile(path)`, `statfs(path)`, `cpuCount()`, `load()`, `memory()` and
`platform`, with native Node defaults. Callers can inject `machineResources`
with the same input/output contract; policy belongs to those callers.

## Dependencies

Node fs and os supply native local observations only. Native tests cover this port.

<details><summary>Runtime interface</summary>

```json
{
  "kind": "native-only",
  "status": "draft",
  "prose_sha256": "f42374b4a5eccdb7aaf6fd07e3329be3de373ffa1abfac10acc3ac985a783952",
  "reason": "This is the native machine-observation port; native tests cover the port. Native evidence owners: test/machine-resources.test.mjs."
}
```
</details>
