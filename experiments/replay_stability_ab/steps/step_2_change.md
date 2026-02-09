# Change Request: Add Email-Based Input (Step 2)

Update `parse_user_id` in `src/user_id_parser.py` to also accept email-format strings:

- Input format: `"email:user@example.com"`
- Extract the username part (everything before the `@`).
- Apply the same validation rules as other inputs:
  - 3-20 chars, alphanumeric + `_` and `-`, lowercase, not reserved.
- Return `None` if:
  - No `@` found after the `email:` prefix.
  - The extracted username is invalid.

The batch function `parse_user_ids` should automatically support email inputs (it delegates to `parse_user_id`).

## Acceptance Tests

All tests in `tests/test_acceptance_step_2.py` must pass (includes all step 0-1 tests):

```bash
pytest -q tests/test_acceptance_step_2.py
```
