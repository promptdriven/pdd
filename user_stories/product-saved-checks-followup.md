# Read saved product checks efficiently

I can continue a product run with my saved Check results, including results saved without an intent label, and see file edits on my next command.

## Acceptance criteria

1. In one product status, next or start command, batches compared with the same folder and selected tests share one source capture even when the test order differs; different folders or test sets use separate captures.
2. Each batch is compared with its own saved source hash, and a later command captures files again so an edit cannot reuse a previous current result.
3. Saved Check batches without an intent label count when every saved row has complete original Check information and the existing source and receipt checks pass, including when criterion text metadata is absent but all authored criterion IDs remain in the stored checks; lint, Try and other explicit intents do not count.
4. Multiple batches without an intent label that lack complete original Check information or complete receipt criterion coverage count no passing Stories and show one hint that older checks are not counted and I should run pdd check again.
5. A failed source capture can be reused only within that command and leaves its results unverified; the next command retries the capture. Reading saved checks makes no Runtime request, changes no saved check and dispatches no work.

## Rules to check

The runtime client owns source matching and compatibility. One command may share
a captured source hash across matching folder and test-set keys; it must compare
every saved hash independently. No memo outlives the command. Standalone saved
evidence reads each have their own scope.

Missing intent requires every saved row to meet the same complete Check-row
predicate used by saved-lint continuation. Explicit Check intent keeps its
existing rules; explicit other intent never becomes Check intent. Compatibility
does not weaken source matching or terminal receipt validation, recover missing
receipts, authorize dispatch, approve a prompt or complete a workflow.
