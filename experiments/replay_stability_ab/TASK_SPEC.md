# Task Spec: Replay Stability Change Request

Apply the same change request in both arms.

## Change Request

Update `parse_user_id` in `src/user_id_parser.py`:

1. Keep existing support for strings like `"user:abc123"`.
2. Add support for dict input: `{"user_id": "abc123"}`.
3. Trim surrounding whitespace from extracted ids.
4. Return `None` for invalid input (missing key, blank id, wrong prefix, non-string id).
5. Never raise for expected bad input (`None`, wrong type, malformed payload).

## Acceptance Criteria

All tests in `tests/test_task_acceptance.py` must pass:

```bash
pytest -q tests/test_task_acceptance.py
```

## Arm Rules

1. `Agentic-Only`:
   implement behavior by directly patching code.
2. `PDD`:
   update prompt first (`prompts/user_id_parser_python.prompt`), regenerate code, then validate.
