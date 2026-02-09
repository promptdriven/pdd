# Change Request: Structured Result — BREAKING CHANGE (Step 4)

**This is a breaking change to the return type.**

Update `src/user_id_parser.py`:

### 1. Define `ParseResult`

```python
import collections
ParseResult = collections.namedtuple("ParseResult", ["user_id", "source"])
```

`ParseResult` must be importable: `from user_id_parser import ParseResult`.

### 2. Update `parse_user_id` return type

Instead of returning `str | None`, return `ParseResult | None`.

- `ParseResult.user_id` — the validated user ID string (same value as before).
- `ParseResult.source` — a string indicating input type:
  - `"string"` for `"user:<id>"` input
  - `"email"` for `"email:user@domain"` input
  - `"dict_flat"` for `{"user_id": "<id>"}` input
  - `"dict_nested"` for `{"user": {"id": "<id>"}}` input
- Return `None` for invalid input (unchanged).

### 3. Update `parse_user_ids` return type

Returns `list[ParseResult | None]` instead of `list[str | None]`.

## Acceptance Tests

All tests in `tests/test_acceptance_step_4.py` must pass. **Note:** All previous tests have been updated for the new return type — they now check `.user_id` on the result.

```bash
pytest -q tests/test_acceptance_step_4.py
```
