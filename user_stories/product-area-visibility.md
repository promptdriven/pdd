# See which product part handled a step

As a product author, I want to see which product part handled a step, so that I can try the complete product confidently.

## Acceptance criteria

1. While my product runs, each step with a declared owner shows its part name, including background server work.
2. After a reload or a completed tap, the same recorded steps keep their part names and existing call counts.
3. A step with no declared owner does not get an invented part name, and reading or showing a label makes no AI call.

## Verification scope

Runtime presentation and admitted ownership metadata. Cases: [native behavior cases](../test/product-composition/product-area-visibility-cases.json). These are requirement drafts, not executed tests or a Runtime pass. Native integration must exercise the real public boundary and preserve all existing request, source and accounting guards.
