# Module binding inventory

`pdd test`, `pdd lint` and `pdd test --files` show declared module coverage for the selected Stories. Bound means a selected test reaches an executable prompt; it does not mean the module passed. Without an inventory, pdd reports coverage unavailable.

Create a Git-visible `pdd-bindings.json` at the repository root:

```json
{"schema_version":"pdd.bindings.v1","modules":[
  {"module":"src/orders.mjs","stories":["user_stories/order.md"],"prompt":"prompts/orders.prompt.md"},
  {"module":"src/printer.mjs","stories":["user_stories/order.md"],"reason":"The physical device acknowledgement is not represented yet.","port_attempt":"Tried a fixed-answer printer port; its device acknowledgement still needs a contract."}
]}
```

The inventory is limited to 64 KiB and 1000 module declarations. The root has exactly `schema_version` and `modules`. Each module has `module`, a nonempty `stories` array and exactly one of: `prompt`, or both `reason` and `port_attempt`. The inventory itself and all declared paths must be existing repository-relative regular Git-visible files without symlinks at the path or any ancestor; safe source-upload link acceptance does not relax this inventory rule. Story paths must name discovered Stories. Module paths must be unique; Story paths within an entry must be unique. Explanations must be nonblank strings. Unknown fields and invalid declarations are lint problems. Bound prompt paths must have an executable Runtime interface and be reached by the selected tests, including declared prompt calls. A navigation link alone does not bind a module.

Before declaring a module unbound, attempt an injected port for outside state or effects and record why it does not cover the required behavior. pdd prints each selected unbound module and both explanations beside `N of M modules bound`. The inventory itself stays local unless separately selected as source context.
