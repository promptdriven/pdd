# Keep required labels inside their matched regions

I can trust a drawing comparison to reject a missing label inside its matched box, even if the same words appear elsewhere.

## Acceptance criteria

1. A painted box passes its id check, but READY outside that matched box cannot satisfy the owned label: the label is missing and the comparison fails.
2. A visible READY label nested in the matched box or painted on the box itself passes when geometry and order match.
3. A hidden READY label inside the matched box remains hidden and fails, even when a visible READY copy exists outside.
4. A reference label without a matched enclosing id can still match visible page text globally.

## Rules to check

When the drawing label belongs to a uniquely matched enclosing id, candidates are only that page element's own text and descendants. An empty owned candidate set means missing; hidden owned candidates mean hidden. Outside copies cannot change either result to pass. Without a matched enclosing id, candidates remain global. Existing occurrence consumption, visibility, geometry, order and table rows still apply.

Forbidden result: a painted matched box and only outside READY produce a passing owned READY row or passing comparison.

## Scope

The cases use newly written synthetic browser snapshots and a simple box drawing. Supplied snapshots check the decision over ownership facts. Real DOM capture, browser effects and public CLI exits require separate native evidence. The broader drawing workflow remains in [Keep the screen aligned with its drawing](svg-layout-spec.md).

Runtime prompt check: Not run. The existing native module has no faithful registered runtime binding. The JSON cases are portable native vectors, not an interpreter scenario. Native public CLI/browser replay supplies the implementation evidence.
