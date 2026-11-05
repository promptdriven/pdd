# Check compatibility before paid work

I can start selected work knowing its compatibility blockers stop paid dispatch while independently ready work can continue.

Draft expectations for person review. No expectation is approved.

## Acceptance criteria

1. A selected test with its own normal lint pass, complete supported compatibility and matching captured source and confirmed job build can start paid work; its business result still requires execution.
2. A selected invalid-source, unsupported-capability or missing-binding blocker stops that test before any paid check or Simulator setup is sent and exits 4 when it is the only selected test.
3. A selected report that is absent, malformed, conflicting, incomplete or unknown, or whose source/build association is unavailable or mismatched, stops new paid work and exits 5 after lint ends; unfinished or lost lint keeps exit 3 and same-ID recovery.
4. One blocked or unchecked test does not stop an independently admitted selected test, and unrelated inventory diagnostics do not become selected blockers.
5. The same selected gate applies to new checks, Simulator setup, saved-lint continuation, retry and a confirmed restart replacement, with the same saved source, owner and dispatch guards.
6. Compatibility analysis sends no wider source archive, supplies no missing fixture fact, alters no approval or behavioral evidence record, and never retries an uncertain paid dispatch.
7. Unproved installed-engine, host or physical-observation claims stay unproved without a new global proof gate; known source/build disagreement still blocks structural admission.

## Rules to check

Paid dispatch requires the selected normal lint pass and the admitted compatibility evidence. For criteria 2 and 3, source/build association comes first: unavailable or mismatched association stays unknown and ends held with exit 5, preserving any raw server blocker as reported. With matched association, a concrete selected blocker refuses with exit 4 even with incomplete selected coverage. Without that blocker, ended incomplete or unknown readiness is held with exit 5. A test's own refusal or a reached prompt's refusal still applies. Open lint keeps exit 3 and same-ID recovery.

The forbidden result is a paid POST for a held test, duplicate uncertain dispatch or widening of selected source. Missing physical proof alone adds no new global gate.

## Native cases for the code step

[Cases](../test/runtime-compatibility/runtime-compatibility-before-paid-work-cases.json) name the existing public outcome, projection and client boundaries for later replay. Runtime check: NOT REPLAYED. The present interfaces do not bind the real capture/archive, transport, saved files, streams and dispatch claims. These are native fake-engine expectations, not executable Runtime scenarios or passing checks. The code step must replay every case with ordinary Node tests and actual temporary state; native profiles remain separately owned.
