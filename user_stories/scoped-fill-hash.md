# Fill hashes for selected work

As a person preparing prompts, I can fill draft interface hashes for selected work so unrelated drafts stay untouched.

## Acceptance criteria

1. Selecting a Story or test fills eligible interfaces it uses, including required prompt dependencies, and leaves unrelated prompt bytes unchanged.
2. Multiple Story, test, path and directory selections use their union, including shared dependencies once; paths work from a subdirectory. An explicit prompt file selects it and its required prompt dependencies even without tests.
3. An unknown or untested selection, malformed selected test, or unsafe or unavailable required dependency refuses before any hash is written, without falling back to all prompts.
4. With no selection, hash filling works without tests and reports each changed file. Existing current, stale, refused and warning outcomes, byte preservation, ordering and exit rules remain in force.
5. Compact mode still rejects operands and incompatible options before writes. Hash filling does not use authentication, network or AI.

## Rules to check

- No unrelated prompt may be written when selections are supplied.
- An unknown or untested operand, malformed selected test, or unsafe or unavailable required dependency prevents all writes, including otherwise valid selections.
- After selection and closure validation, an individual interface refusal may coexist with successful fills of other selected interfaces.
