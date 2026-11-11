# Admit a selected Runtime contract

PDD keeps the authored interface and uploads its executable declaration to Runtime.
For example, an authored `kind: partial` interface can declare one operation from
a larger module. The uploaded interface contains those same operations and schemas.
PDD removes only the top-level `kind` metadata. It keeps the authored file, approval
state and prose hash. This does not assert that the whole module was checked.

`pdd lint STORY` checks admission without an AI call. A successful lint is not an
executed behavior check. Use `pdd test STORY` for that check and inspect its receipt.

## Give each entry its own resources

Without `resource_operations`, every entry sees every resource in its interface.
If one entry needs a process port and another is pure, declare their scopes:

```json
{
  "operation": "inspect",
  "input_schema": {"type": "object", "properties": {}, "required": [], "additionalProperties": false},
  "result_schema": {"type": "object", "properties": {}, "required": [], "additionalProperties": false},
  "errors": [],
  "resource_operations": []
}
```

The other entry can declare `"resource_operations": ["process.run"]`. Once any
entry declares this field, every entry must declare it. Use qualified operation
names from the interface resources. Their union must cover all declared resource
operations. Keep each list faithful to that entry's actual dependency contract.
Local binding advice uses a valid selected-entry scope while retaining all
required source files. Other context modules keep conservative binding advice.
Malformed or incomplete scopes cannot suppress that advice; Runtime judges admission.

A process is a `port` resource named `process` with a `run` operation. Its schemas
describe the injected process runner's real arguments and result. A `port.write`
simulation records those arguments in the scenario world and returns the declared
fixture result. It does not run an operating-system process. Actual process and
adapter integration still needs native evidence. See [Runtime boundaries](runtime-boundaries.md).

Do not add replies for resources an entry cannot use. Do not remove a resource it
does use to obtain a pass. Existing missing bindings and conflicting active resource
declarations still need repair.

## Read a refusal

An invalid interface remains invalid after transport. Complete Runtime lint can
report a JSON Pointer such as `/entries/0/errors`: the `errors` field of the first
entry. `/kind` on a direct Runtime upload identifies PDD metadata that was not
projected by PDD. A refusal from an older server can have only a parent location;
the Runtime service must support precise field diagnostics to report child locations.

Hash advice is module-level advice and has warning severity. A selected entry that
only returns a supplied digest needs no compute call. If it builds or verifies a
hash, declare the corresponding compute resource or keep that criterion in native
tests. An advisory message does not establish which entry actually computes a hash.

Approval, required source context, truthful partial scope and the full native suite
remain separate requirements. Admission cannot supply missing evidence for them.

If the owning prompt deliberately leaves an operation out of its Runtime interface,
adding fixture replies does not make that operation executable. Keep its native
scenario vectors outside Runtime JSON test discovery and run their normal native
tests. For example, saved-workspace evidence uses
`node --test test/import-authorized-workspace-evidence.vectors.test.mjs` for its
19 original cases. Those native results do not claim an AI Runtime pass or fill
missing resource bindings.
