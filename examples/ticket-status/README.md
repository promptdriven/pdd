# Synthetic ticket-status example

This fictional example defines a tiny status-labeling function. The prompt is the behavior contract; the Story lists observable criteria; the JSON file gives example inputs and independent expected results. The JavaScript implementation is written to match the prompt so that its behavior can be inspected and replayed locally. No PDD runtime generation or runtime vector execution is claimed.

The JSON shape in `vectors/status-labels.json` belongs to this example and its Node test. It is not a native PDD vector schema. The Node test is an ordinary public code test, not a PDD prompt check or formal proof.

From the repository root, run:

```sh
node --test examples/ticket-status/test/status.test.mjs
```
