# Start a product without hidden setup problems

As a product author, I want to start a product without hidden setup problems, so that I can try the complete product confidently.

## Acceptance criteria

1. A small product can start without shared world or shared seed files, using its part data or an empty world.
2. An unrelated Notes table does not change who may write orders.
3. If a tap could need more than 40 AI calls, PDD refuses before upload; a tap needing exactly 40 remains eligible.
4. Malformed, unsafe or ambiguous source settings give an explanation and leave my files unchanged.

## Verification scope

PDD CLI composition and orchestration. Cases: [native behavior cases](../test/product-composition/product-composition-guards-cases.json). These are requirement drafts, not executed tests or a Runtime pass. Native integration must exercise the real public boundary and preserve all existing request, source and accounting guards.
