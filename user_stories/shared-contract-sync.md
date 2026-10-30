# I preview and apply moving copies to references

## Acceptance criteria

1. Sync previews unique exact or near copy replacements without writing files.
2. Sync with --write adopts the selected shared schema and preserves local title and description.
3. Ambiguous copies stay unchanged while independent unambiguous copies can migrate.
4. Editing an approved interface sets it to draft without approving it.
5. All bytes outside replaced schema values and an approved-to-draft status stay exact, and a repeated sync makes no further changes.
6. Sync refuses an unsafe destination or concurrent source edit without overwriting it.
7. A successful sync replaces the complete file atomically; a failed write leaves the complete original.

## Rules to check

A near-copy preview exposes every semantic difference before --write adopts the canonical shape. Only selected schema values and the approved-to-draft status value may change; preserve every other byte, including key order, spacing and newline style. Use a safe temporary file and atomic rename; refuse a changed/symlink destination before replacement. Preview and write make zero runtime calls. The approved prose hash is not a contract-content approval.

Runtime check: native effects unbound: file/history/write cases specified separately; expansion cases do not establish these effects.
