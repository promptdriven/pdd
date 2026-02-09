# Change Request: Add Batch Processing (Step 1)

Add a new function `parse_user_ids` to `src/user_id_parser.py`:

```python
def parse_user_ids(items: list) -> list[str | None]:
```

- Process each item through the existing `parse_user_id` function.
- Preserve input ordering: `result[i]` corresponds to `items[i]`.
- Handle mixed valid/invalid inputs (invalid items produce `None` in that position).

## Acceptance Tests

All tests in `tests/test_acceptance_step_1.py` must pass (includes all step 0 tests):

```bash
pytest -q tests/test_acceptance_step_1.py
```
