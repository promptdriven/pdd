# I see advice about differing inline copies

## Acceptance criteria

1. Explicit lint advises when a copied schema differs with the same fields or one extra or missing field.
2. Changing a nested constraint is visible even when the field names stay the same.
3. Equal copies and schemas differing by two fields produce no drift advice.
4. Ambiguous matches warn without choosing a record.
5. Drift advice leaves the server lint result and exit status unchanged.

## Rules to check

Use working files, schema positions and canonical comparison. Existing references and literal annotations/inputs/expectations are not copies. Advice never changes expected values. Ordinary preliminary lint does not scan for drift.

Runtime check: native effects unbound: file/history/write cases specified separately; expansion cases do not establish these effects.
