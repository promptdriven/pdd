# Native typed-call adapters

`pdd test --target code` can execute a project-supplied adapter for a typed operation. The adapter calls the real native application and injects the scenario's saved resource replies. Supported resources are `port` and read-only `command`, both backed by the bounded recorded fixture below. PDD evaluates the original checks with zero interpreter or AI calls. The adapter is trusted project code; PDD does not sandbox its filesystem or network access.

Declare exactly these fields in the tested entry's local implementation metadata:

```json
{
  "kind": "call",
  "command": ["node", "examples/fakes/service.mjs"],
  "symbol": "lookup"
}
```

`command` is a nonempty array of literal strings; its executable is nonblank. `symbol` is a nonblank string interpreted by the adapter. No string may contain NUL. There is no shell expansion. Unknown metadata keys or kinds are unsupported. This declaration is for the native code route. The installed interpreter admission supports CLI implementation metadata only; ordinary prompt checks must use the original prompt without this local call declaration. Do not treat a native pass as an interpreter pass.

The adapter reads one UTF-8 JSON object from stdin. Every request has exactly these fields:

| Field | Meaning |
| --- | --- |
| `schema_version` | Exactly `prompt-runtime.code-call.v1` |
| `operation` | The scenario step's declared operation string |
| `symbol` | The implementation's declared symbol string |
| `input` | The original step input object |
| `initial_world` | The current scenario world object; initially the original `initial_world` |
| `simulation` | The original simulation object; absent simulation becomes `{}` |

The adapter writes one JSON object to stdout, with optional surrounding whitespace, and exits 0. Every response has `schema_version` with the same version, `world` (the complete world object after the step), `calls` and exactly one of `result` or `error`. No other keys are allowed. `result` must satisfy the entry's result schema. `error` has exactly `code`, one of the entry's declared error strings. `calls` has exactly `resources` and `internal`, each an object mapping Runtime counter names to nonnegative safe integer counts for that step. This route has no internal prompt calls, so `internal` is empty. Count actual application resource calls, including zero for unused declared operations. For prompt `service`, port `service.lookup` uses `/resources/service-service-lookup`.

All JSON values retain their meaning. Plain whole-number tokens outside the safe Number range retain their exact digits through input, world, fixture results, response comparison and reports. Use an exact JSON reader/writer, such as PDD's `parseScenarioJson` and `stringifyScenarioJson` for Node adapters. Never round, stringify integers as data strings, or introduce tagged integer objects. Fraction/exponent tokens retain the ordinary scenario Number meaning.

The supported saved resource binding is `fixture.lookup`. Each binding has exactly `action`, `world_pointer`, `cases`, `result_template` and `result_value_pointer`. `action` is `fixture.lookup`, `result_template` is null and `result_value_pointer` is empty. `world_pointer` selects a nonnegative safe integer counter in the world. `cases` is a nonempty array of exact `{args, call_index, result}` objects; `args` is the complete resource argument object and `call_index` is a unique positive safe integer. At each actual resource call, advance that resource's counter by one and select the case whose index and complete arguments both match. Supply its literal result to the native application. Preserve other world values. Counters persist across steps; call counts reset each step.

For a recorded `command` resource, both the resource and its operations retain read access. Keep the original resource kind and argument/result schemas; validate the saved arguments and literal reply against those schemas. For example, an operation `client.status` can accept `{}` and receive a saved structured locale reply. It remains a command-resource observation; it is not converted into a port or executed as a live command. No raw command-output parsing, live command launch or replacement reply is added. The request/response envelope and original Story checks are the same for both supported resource kinds.

Missing matches, malformed bindings, overlapping counter paths, unsupported effects or actions must stop the adapter without a successful protocol response. They must never fall back to a live command, service or model. The adapter supplies this resource bridge; PDD does not generate language-specific adapters or infer native function signatures.

The synthetic service example retains its exported `lookup(service, id)` API and also acts as an adapter when executed directly. Its native fixture copy adds the local metadata above without changing the Story scenario. Run that copy with `pdd test --target code fake-recorded-call --json`. The repository's ordinary prompt-check copy omits this metadata. Native process execution, source admission and exact integer transport require the repository's native tests; a prompt check of the lookup flow does not establish those effects.

## Verify the native route locally

Prerequisites: Node 22.16 or later, Git and this checkout's pinned npm dependency. Use the normal repository setup (`npm ci`) when dependencies are absent. These checks need no provider credentials or interpreter connection.

From the repository root, run the affected public-boundary tests:

```sh
node --test test/compiled-story-tests.test.mjs test/compiled-call-tests.test.mjs test/fake-recorded-call.vectors.test.mjs
```

The replay test creates a private Git project. It copies the service prompt, adapter, contract, Story and saved scenario from this checkout. It adds native implementation metadata only to that project's prompt copy. The canonical Story and scenario stay byte-identical. The actual PDD CLI launches the actual native application, checks all eight assertions, records the commit and writes `.pdd/code-test/latest.json` in the private project. A separate control changes the native label; both original label assertions must fail while both steps still execute. Each test cleans its own project.

For an inspectable manual run, keep the fixture until inspection finishes. Run setup from the repository root:

```sh
pdd_source="$PWD"
fixture_root="$(node --input-type=module - <<'JS'
import {fixtureProject} from './test/helpers/code-call-project.mjs';
console.log(fixtureProject());
JS
)"
```

Perform the real action from the private project:

```sh
cd "$fixture_root"
node "$pdd_source/bin/pdd.mjs" test --target code fake-recorded-call --json
cat .pdd/code-test/latest.json
```

Expect exit 0, `ai_calls: 0`, two passed steps and four passed checks per step. The labels are Available then Reserved. The world counter is 1 then 2; each step reports one resource call. No live service runs.

Plant one wrong native answer while retaining the original saved replies and checks:

```sh
node --input-type=module - <<'JS'
import {readFileSync,writeFileSync} from 'node:fs';
const path='examples/fakes/service.mjs';
const text=readFileSync(path,'utf8');
writeFileSync(path,text.replace('return service.lookup({ id });',
  "return {...service.lookup({ id }),label:'WRONG_NATIVE_ANSWER'};"));
JS
node "$pdd_source/bin/pdd.mjs" test --target code fake-recorded-call --json
```

Expect exit 1 with failed original label assertions. A launch error or a not-run step does not establish this control. Inspect the report before cleanup. Return to the checkout and remove the private project:

```sh
cd "$pdd_source"
node --input-type=module - "$fixture_root" <<'JS'
import {clean} from './test/helpers/code-call-project.mjs';
clean(process.argv[2]);
JS
```

The committed bounded check covers every offset from -2 through 2 around -2^53, 2^53 and 2^63-1, plus every initial fixture counter from 0 through 3 with two ordered calls. A fresh formal checker runs it and its semantic controls:

```sh
node --test test/fake-recorded-call.formal.test.mjs
PDD_NATIVE_FORMAL_CONTROL=integer node --test test/fake-recorded-call.formal.test.mjs
PDD_NATIVE_FORMAL_CONTROL=counter node --test test/fake-recorded-call.formal.test.mjs
```

The normal run must pass. Each control must fail an assertion after native execution, with `FORMAL_EXACT_INTEGER` or `FORMAL_ORDERED_COUNTER` respectively. These bounded checks do not prove arbitrary adapters, production effects or prompt/code equivalence. The independent verifier also runs the public full suite with `npm test`.
