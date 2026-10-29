# See declared module coverage

I can see which declared modules the selected Stories cover and why each other module remains unbound.

## Acceptance criteria

1. For the selected Stories, pdd prints the number of declared modules bound and every unbound module with its reason and attempted port.
2. A missing or blank unbound reason or attempted port is a lint problem.
3. A prompt that selected tests do not reach cannot claim a module is bound.
4. Without a module inventory, pdd says coverage is unavailable.

## Rules to check

Attempt a runtime port before declaring a module unbound. Coverage counts unique declared modules for the selected Stories; it does not infer coverage of undeclared code or equate binding with passing checks. Explicit lint sends no checks and makes no AI calls.

Verification: `node --test test/runtime-binding-coverage.test.mjs` exercises selected Story reporting and lint refusals with a fake service; it makes no model calls.
