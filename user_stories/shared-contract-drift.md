# I see advice about differing inline copies

## Acceptance criteria

1. Explicit lint advises when a copy with at least three fields differs from a shared record with at least four fields by constraints or one extra or missing field.
2. Changing a nested constraint is visible even when the field names stay the same.
3. Equal copies and schemas differing by two fields produce no drift advice.
4. Ambiguous matches warn without choosing a record.
5. Drift advice leaves the server lint result and exit status unchanged.
6. Empty, one-field and two-field inline schemas are skipped; an equal three-field record can match exactly, but a differing three-field record gives no near advice.
7. Reordering required fields or enum alternatives gives no drift advice; changing the order inside literal array values still does.

## Rules to check

Use working files, schema positions and canonical comparison. Existing references and literal annotations/inputs/expectations are not copies. A three-field equal copy can migrate exactly; near matching requires a canonical record with at least four fields and an inline copy with at least three. Only schema required/enum ordering is ignored; nested literal arrays retain order. Advice never changes expected values. Ordinary preliminary lint does not scan for drift.

Runtime check: native effects unbound: file/history/write cases specified separately; expansion cases do not establish these effects.
