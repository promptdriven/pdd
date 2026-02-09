# Change Request: Strict Mode (Step 5)

Update function signatures in `src/user_id_parser.py`:

### `parse_user_id`

```python
def parse_user_id(raw, reserved_ids=None, strict=False) -> ParseResult | None:
```

- When `strict=True`, additionally reject IDs that contain consecutive special characters:
  - `__` (double underscore)
  - `--` (double hyphen)
  - `_-` (underscore followed by hyphen)
  - `-_` (hyphen followed by underscore)
- When `strict=False` (default), behavior is unchanged from step 4.
- Must work with all input types (string, email, dict).

### `parse_user_ids`

```python
def parse_user_ids(items: list, reserved_ids=None, strict=False) -> list[ParseResult | None]:
```

- Pass `strict` through to each `parse_user_id` call.

## Acceptance Tests

All tests in `tests/test_acceptance_step_5.py` must pass (includes all step 0-4 tests):

```bash
pytest -q tests/test_acceptance_step_5.py
```
