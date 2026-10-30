# Refuse invalid Runtime interface limits locally

I can find and fix limits the runtime would refuse before a check uploads my prompt or asks for authentication.

## Acceptance criteria

1. A prompt with max_steps or max_model_calls set to 0 is refused locally with invalid-limits, its prompt path, the field, and a fix that says to use an integer of at least 1. The same applies to negative, fractional, Boolean, string and null limits.
2. Limits must contain exactly max_steps and max_model_calls. A missing limits object is invalid-interface; a wrong object shape or missing or extra limit field is invalid-limits. The refusal names the problem and how to fix it.
3. Integer limits of 1 and larger pass the local limits check without an invented upper bound. Decimal and exponent spellings such as 1.0 and 1e0 are refused as invalid-limits, matching runtime execution admission, including when ordinary number parsing would round away a fraction.
4. A bad limit in a prompt called by the selected prompt is also refused locally, naming that called prompt. An unrelated unselected prompt does not block the selected Story, and existing schema and hash refusals still apply.
5. With a refused limit, a normal check or server-lint command returns exit 4 without reading authentication or contacting the runtime. The prompt and test files remain unchanged.

## Rules to check

The Runtime interface has exactly two limit fields, max_steps and max_model_calls, with integer JSON literals of at least 1 and no upper bound. No rejected limit may be reported as ready or sent by a normal check. The server-lint command keeps server diagnostics for every other problem.
