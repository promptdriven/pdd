# Capture the synthetic native replay test

`capture.mjs` runs the example's Node test from the repository root and writes
the Node test event stream and companion source, selection and execution records
into `DIRECTORY`, its first argument. Its optional second argument is `current` (default) or `before`; any other arguments fail. It writes `report.json` (Node events), `source.json`, `selection.json`, `execution.json` and `import.json` (a `pdd.native-evidence-import.v1` descriptor). It writes an import descriptor for
`replay` and its Story. Capture the selected source before and after the test;
if it changes, exit nonzero without writing evidence. Record every emitted event in order, including diagnostic events and error details. Preserve the original event data alongside the reader-facing data, whose file path is repository-relative. Serialize Error name, message, stack and own properties, including nested causes and assertion values. Record the actual completed process outcome and event identities, not invented expected test results. The caller
associates the same selected source with the workflow before importing the
records. This example records evidence; it does not approve a gate or claim a
Runtime check.

## Dependencies

Node's test runner supplies events. The repository's source capture reader supplies
the selected source hash; the replay profile supplies the selected paths.
