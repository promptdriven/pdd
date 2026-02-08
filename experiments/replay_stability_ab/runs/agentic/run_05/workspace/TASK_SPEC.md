# Task Spec (Medium): Robust User ID Parsing

Apply the same change request in both arms.

## Change Request

Update `parse_user_id` in `src/user_id_parser.py`:

1. Accept string input in form `"user:<id>"`.
2. Accept dict input in either form:
   - `{"user_id": "<id>"}`
   - `{"user": {"id": "<id>"}}`
3. Normalize extracted IDs:
   - trim surrounding whitespace
   - lowercase the final result
4. Enforce validity:
   - allowed characters: `a-z`, `0-9`, `_`, `-`
   - length between 3 and 20 inclusive
   - reject reserved IDs: `admin`, `root`, `system`
5. Return `None` for invalid input.
6. Never raise for expected bad input types or malformed payloads.
7. Do not mutate input dictionaries.

## Acceptance Criteria

All tests in `tests/test_task_acceptance_medium.py` must pass:

```bash
pytest -q tests/test_task_acceptance_medium.py
```

## Arm Rules

1. `Agentic-Only`:
   implement behavior by directly patching code.
2. `PDD`:
   update prompt first (`prompts/user_id_parser_python.prompt`), regenerate code (prefer `pdd --force sync user_id_parser`), then validate.
