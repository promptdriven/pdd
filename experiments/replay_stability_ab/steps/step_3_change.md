# Change Request: Configurable Reserved IDs (Step 3)

Update function signatures in `src/user_id_parser.py`:

### `parse_user_id`

```python
def parse_user_id(raw, reserved_ids=None) -> str | None:
```

- When `reserved_ids` is `None`, use the default set: `{"admin", "root", "system"}`.
- When a set is provided, use **that set instead** (replaces defaults entirely).
- An empty set means nothing is reserved.

### `parse_user_ids`

```python
def parse_user_ids(items: list, reserved_ids=None) -> list[str | None]:
```

- Pass `reserved_ids` through to each `parse_user_id` call.

## Acceptance Tests

All tests in `tests/test_acceptance_step_3.py` must pass (includes all step 0-2 tests):

```bash
pytest -q tests/test_acceptance_step_3.py
```
