# Start my Try after slow lint

I can start my Try from an agent shell when lint takes longer than 90 seconds but finishes within the existing five-minute setup allowance.

## Acceptance criteria

1. `pdd simulate place-order --app-map app-map.json --max-calls 40 --no-open --no-wait` waits for lint that passes after 122 seconds in either an agent shell or a terminal, then creates one Try with that app map and ceiling of 40 calls, without another lint upload.
2. Lint, local admission, maintenance, retry backoff and Try creation share one five-minute setup allowance; passing lint does not grant another five minutes.
3. Pending or unknown lint creates no Try; lint that ends without a pass for the selected test remains final not run with exit 5, and a lint refusal remains exit 4.
4. Interruption or exhaustion of the setup allowance sends nothing further; an accepted or uncertain request is read by its original ID and is never repeated automatically.
5. `--no-wait` affects collection after the Try is ready and never bypasses lint; no new Try timeout flag or saved Try-lint continuation is required.

## Rules to check

The [runtime client](../prompts/cli/runtime-client.prompt.md#retry-confirmed-lint-capacity-refusals) owns this wait. Starting at remote setup admission, every setup stage consumes the same 300000 milliseconds. A new Try dispatch requires the selected test's own lint pass, remaining setup time and no interruption. Forbidden: a separate 90000-millisecond agent lint cutoff, a reset clock after lint, or Try dispatch at/after the deadline or without a pass. Confirmed not-started capacity recovery retains its existing safeguards; accepted or uncertain submissions never gain retry permission from this longer wait.

## Expected native cases

All cases use synthetic transport and clock replies with real temporary Git/state; no live service is needed. Each row is one command/action, with observations derived from the proposed criteria for the person's review.

| Case | Supplied input/world | Required observation |
| --- | --- | --- |
| Agent slow lint (AC1, AC5) | Exact command above; noninteractive; lint passes at 122000ms; Try immediately ready | exit 0 at 122000ms; one lint POST and one Try POST; original source/seed, app_map app-map.json and max_calls 40 retained; zero Check POSTs |
| Terminal control (AC1) | Same world and command; interactive | Same result and dispatch counts as agent |
| Last available time (AC2) | Lint passes at 299000ms; Try immediately ready | exit 0; one lint and one Try; no reset of setup deadline |
| Pending boundary (AC2, AC3) | Lint remains running through 300000ms | exit 3 at 300000ms; pending wording; one lint POST, zero Try/Check POSTs |
| Shared remainder (AC2, AC4) | Lint passes at 240000ms; confirmed not-started Try capacity reply; waits exceed remaining 60000ms | stop at 300000ms; no later POST or fresh five-minute wait; no accepted Try created |
| Admission consumes budget (AC2, AC4) | Separately local slot or maintenance unavailable until 300000ms, before lint POST | exit 5; zero lint/Try/Check POSTs; name the wait that ended |
| Terminal no pass (AC3) | Lint ends at 122000ms; selected test has no passing verdict or refusal | exit 5 immediately; final not-run reason; zero Try/Check POSTs |
| Refused (AC3) | Lint ends at 122000ms refusing the selected test | exit 4; refusal reason retained; zero Try/Check POSTs |
| Unknown (AC3, AC4) | Separately explicit unknown lint, wrong-ID/command receipt or lost lint reply that remains unresolved/unknown after same-ID reads | zero Try/Check POSTs; uncertain dispatched lint is read only by its original ID; no replacement lint without confirmed safe capacity evidence |
| Interrupt (AC4) | Interrupt after 122000ms while lint runs, or after lint passes before Try dispatch | no subsequent ID allocation or POST; interruption wording retains submission history |
| Lost lint reply resolves (AC1, AC2, AC4) | Exact command above; lint POST reply lost; same-ID read confirms the selected test passes at 122000ms; Try immediately ready | exit 0 at 122000ms; one lint POST and one Try POST; no new lint ID or upload; original source/seed, app_map app-map.json and max_calls 40 retained; zero Check POSTs |
| Lost Try reply (AC4) | Lint passes at 122000ms; Try POST reply lost; same-ID read confirms ready | exactly one Try POST; read same ID; source/app map/cap retained |

Runtime check: BLOCKED (#2548). The owner has no Runtime interface for runTry; Git discovery/capture, hashing/archive and private state/locking/process effects remain unbound. HTTP/clock replies alone cannot execute this Story truthfully on the interpreter. These are reviewable native cases, not an executable Runtime scenario or a claimed pass. Code-space native replay must call the real runTry boundary with temporary Git/state and injected transport/clock/interrupt ports. Check/read continuation and ordinary Check waiting belong to #2815 and are outside this Story.
