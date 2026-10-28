# Offline review and Runtime boundaries

`pdd check --lint` uploads the selected files to the authenticated runtime server. It uses
zero AI calls, but needs a network connection and server capacity. A task that permits only
offline work does not permit this command.

| Offline work | What it establishes |
|---|---|
| `pdd check --files [STORY...]` | The selected upload paths, byte sizes and capture safety checks; nothing is sent. |
| `pdd check --fill-hash` | The hashes of draft interfaces; nothing is sent. |
| Read the prompt, Story and test together | Check declared schemas, exact criterion text, dependencies and expected-value ownership. This is an authoring review. |
| Run the repository's ordinary tests | The native behavior those tests exercise. |

Record the actual checks you performed. Offline review is not a server lint pass or a Runtime
behavior verdict. If server access is outside the task's permission, leave those results
unverified. When server access is allowed, explicit `--lint` requests complete diagnostics and prints the problems the server reports;
correct them and check again before submitting a behavior check.

## Native factories and JSON operations

A Runtime operation needs concrete JSON input, result and error contracts. A public factory
that returns installed owners, callable ports, processes or cleanup methods has a native
contract. An object with those capabilities is not a JSON result merely because its fields can
be named in prose.

For an installed worker-configuration factory, keep the real public factory and its native
return type. Without an available JSON return contract and the installed dependency contracts,
that Runtime conversion is incomplete. Do not replace the return with `{}`, invent a DTO or
adapter, or simulate successful worker startup. Missing installed modules remain missing
context; a dependency link does not supply their declarations.

A real public operation with a JSON contract can be bound within its declared scope. Native
factory construction, owner wiring, process effects and cleanup remain native test obligations.
Report exactly what a Runtime check covers and what remains unbound. A passing JSON check does
not satisfy an unbound native acceptance criterion or approve a workflow gate.

## Read call usage as evidence

A check that pdd never posts has zero check AI calls, including one held behind unfinished lint.
The lint result can remain unknown while that check was not run. `pdd check --read BATCH` reads
existing work and sends no new check.

For a submitted run, keep the server's accounting result. If it reports unknown usage or
incomplete accounting, a raw `provider_calls: 0` does not prove zero cost. Keep the run's call
ceiling reserved until complete evidence resolves it; do not resubmit the same run to obtain a
number. Share its report with the PDD team.
