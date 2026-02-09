# Change Request: Robust User ID Parsing (Step 0 — Full Spec)

Implement `parse_user_id` in `src/user_id_parser.py`:

1. Accept string input in form `"user:<id>"`.
2. Accept dict input in either form:
   - `{"user_id": "<id>"}`
   - `{"user": {"id": "<id>"}}`
3. Normalize extracted IDs:
   - Trim surrounding whitespace
   - Lowercase the result
4. Validate:
   - Allowed characters: `a-z`, `0-9`, `_`, `-`
   - Length between 3 and 20 inclusive
   - Reject reserved IDs: `admin`, `root`, `system`
5. Return `None` for invalid input.
6. Never raise for expected bad input types or malformed payloads.
7. Do not mutate input dictionaries.

## Acceptance Tests

All tests in `tests/test_acceptance_step_0.py` must pass:

```bash
pytest -q tests/test_acceptance_step_0.py
```
