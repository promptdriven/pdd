# Continue my check after slow lint

I can wait for lint or use the saved recovery command to finish my original Story check without repeating lint.

## Acceptance criteria

1. `pdd check p06 --max-calls 6 --timeout 4` waits past 120 seconds for passing lint, then checks only p06 with its original ceiling of 6 calls.
2. Without an explicit timeout, an agent stops waiting at 90 seconds; a terminal Check has no separate lint limit, and standalone remote lint follows the same caller wait.
3. After pending lint passes, `pdd check --read BATCH` or `pdd check --retry BATCH` continues the original held checks using the saved selection and call ceilings without a redundant lint upload or new lint; check POSTs retain their required source multipart.
4. Recovery refuses a changed owner, repository or captured source before allocating a check ID or sending a check, and always uses the saved runtime origin.
5. Repeated or concurrent recovery and interrupted or lost replies never send the same paid check twice; previous IDs, answers and usage remain intact.
6. A standalone lint read sends no paid checks; ambiguous legacy intent, unresolved lint and lint refusals cannot authorize checks.
7. Interactive Try can finish lint after 120 seconds within its existing five-minute setup allowance, while its agent default remains 90 seconds.

## Rules to check

The original request's intent survives waiting. New batches explicitly record Check or lint-only intent. Supported legacy 0.1.9/0.1.10 Check records need the original valid per-row call ceiling, criteria count, authored steps and recognized producer evidence that the row was held for lint (including an already-read legacy result), as specified by the [owning prompt](../prompts/cli/runtime-client.prompt.md#continue-the-original-saved-check); missing or contradictory evidence fails closed. A passing lint alone never authorizes paid checks.

Recovery has a fresh finite caller wait (--timeout when supplied, otherwise 90 seconds). Validate before allocating the first held check ID and claim dispatch exclusively before POST. Preserve posted/running/lost/unknown jobs and every historical ID; never replay them. UUID call reads, hidden request reads and capacity reads remain GET-only. Pending/refused/unknown lint does not become a successful check. No exception changes server permission or execution rules.

## Expected native cases (draft, not executable Runtime scenarios)

Each row is one command/action with deterministic fake clock and transport replies. Follow-up rows retain the prior saved batch. Expected values are requirement-derived; no native implementation change belongs in this prompt draft.

| Case | Input and supplied world | Expected observation |
| --- | --- | --- |
| Explicit wait | Check p06, max-calls6, timeout4; lint passes at150s | one lint, one p06 check; request cap6; exit0 for passing check; elapsed150s, no120s stop |
| Default agent | same selected Check without timeout; lint running at90s | exit3 at90000ms; pending lint ID saved; zero check POSTs/IDs/calls |
| Interactive | terminal Check; lint passes at150s | waits150s; one original check; exit0 for passing check |
| Lint-only wait | remote --lint p06 --timeout 4; lint passes150s | exit0; exactly one lint POST; zero check POSTs |
| Read continuation | saved pending normal Check from agent case; same capture; latest lint passes | one first held check ID and POST; original batch/test/cap6 retained; zero redundant lint uploads/new lint; required check multipart retained; exit0 when passed |
| Retry continuation | separate identical pending batch; --retry BATCH | same continuation guarantees as read |
| Repeat | read completed continuation batch | no new UUID/POST; same result and IDs |
| Concurrent | two recoveries overlap on the same eligible saved batch | one exclusive claim and one paid POST total; the owner keeps the one check ID; an overlapping command exits 3 and sends nothing |
| Lost dispatch | first continuation POST loses response | keep claim/ID; subsequent read GETs that ID, zero replacement POSTs; unknown usage remains unknown |
| Interrupted | interrupt before validation/claim, separately after claim | before: zero new ID/POST; after: never replay claimed ID |
| Identity guards | separately change login, repo or selected file bytes | refusal before ID/POST; all previous saved results retained |
| Saved origin | change current PDD_RUNTIME_URL while retaining saved batch origin | use saved origin for reads and continuation; never redirect saved jobs |
| Source selection | unrelated Story also exists; saved p06 only | recapture saved paths only; no unrelated check; exact saved source SHA required |
| Still pending | latest lint remains running on recovery | exit3; same lint ID; zero paid IDs/POSTs |
| Invalid lint | separately wrong ID, wrong command, unknown, missing receipt, reached/global refusal | no check ID/POST; preserve uncertainty or explain refusal and paths |
| Standalone | saved explicit lint with terminal passing receipt | zero paid IDs/POSTs on read/retry |
| Legacy Check | version1 producer record with valid max_calls6, criteria_total, authored steps and pending evidence | safe same-source continuation without repeat lint |
| Legacy already read | version1 0.1.9/0.1.10 Check with valid max_calls6, positive criteria_total and consistent authored steps; prior read left lint passed with pending/unknown cleared, row phase lint/state not_run with calls omitted by the known producer, no check IDs and note.code lint-finished; matching owner/repo/source and no dispatch claim | one first check ID and exclusive claim, one original check POST without repeat lint; known never-posted state establishes zero calls; same guards apply to prior unknown-lint not_run evidence; positive/unknown/incomplete call evidence if present refuses continuation |
| Legacy ambiguity | legacy standalone missing max_calls/criteria_total; separately contradictory intent | zero paid IDs/POSTs; explain unavailable Check intent |
| Existing jobs | batch includes completed, running, lost and held rows | preserve all prior IDs/answers; only proven never-posted held row gets first ID |
| Recovery deadline | --read BATCH --timeout 4, separately default | fresh bounded240000ms or90000ms wait; no cap increase or extra dispatch after limit |
| Try | interactive lint passes150s; separately agent lint pending90s | terminal proceeds within existing300000ms setup allowance; agent exits3 at90000ms; no Try timeout flag added |

Runtime check: BLOCKED (#2548). The owning module exports real runCheck/runTry with injected transport, clock, gh and interrupt ports, but Git root/discovery/capture, hashing/archive and private RuntimeStore filesystem/locking effects remain native and unbound. The prompt has no Runtime interface metadata. Supplying transport replies alone cannot test this public behavior truthfully; no check-only operation or fabricated Runtime interface is introduced. Code-area native tests must use the real exports and temporary Git/state plus fake transport/clock, cover this table and preserve capacity recovery controls. A future Runtime binding must bind those actual outside effects and preserve handles/callbacks. No Runtime pass or live report is claimed.
