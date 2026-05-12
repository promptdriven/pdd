## Step 8: Test Plan

### Existing Test Coverage
- **Test file:** `tests/test_agentic_update.py`
- **Current coverage:** Covers basic module functionality including success/failure routing, missing files, no agents available, lacking tests directories, formatting exceptions, quiet mode execution, and returning newly discovered test files.
- **Gap:** There is no coverage verifying the bounds of `_revert_out_of_scope_changes` when invoked by `run_agentic_update`. Existing tests implicitly skip the scope guard by not initializing git repositories. Additionally, there is no coverage verifying that `before_paths` and `after_paths` correctly track explicitly included prompt files or new `context/` files to surface them in the returned `changed_files` list.

### Proposed Tests

#### Test 1: Agentic update preserves explicitly included docs
- **Input:** A prompt file that contains an `<include docs/my_doc.md>` tag. A local `git` repository is initialized. The mocked `run_agentic_task` appends text to `docs/my_doc.md`.
- **Expected:** The edits to `docs/my_doc.md` are preserved on the filesystem (State Channel) because parsing the `<include>` tag adds the file to the allowlist.
- **Actual (before fix):** The edits are discarded/reverted by `_revert_out_of_scope_changes`.

#### Test 2: Agentic update preserves new shared context files
- **Input:** A local `git` repository is initialized. The mocked `run_agentic_task` creates a completely new file at `context/shared_state.md`.
- **Expected:** The newly created file is preserved on the filesystem (State Channel) because paths under `context/` are broadly permitted by the prompt specification.
- **Actual (before fix):** The newly created file is deleted/reverted by `_revert_out_of_scope_changes`.

#### Test 3: Unrelated file mutations are reverted
- **Input:** A local `git` repository is initialized. The mocked `run_agentic_task` mutates an unrelated file outside the prompt, code, test, and context paths (e.g. `src/unrelated_file.py`).
- **Expected:** The unrelated file mutation is fully reverted to its original state (State Channel).
- **Actual (before fix):** The unrelated file is reverted (this ensures our fix doesn't break the existing guard behavior).

#### Test 4: Tracking state before_paths initialization captures included docs (Output Channel)
- **Input:** A prompt file with an `<include docs/my_doc.md>` tag. A mocked agent modifies `docs/my_doc.md`.
- **Expected:** Because `before_paths` correctly initializes by parsing includes, `_detect_changed_files` catches the edit. The return tuple's `changed_files` list (Data Flow / Output Channel) includes `docs/my_doc.md`.
- **Actual (before fix):** `before_paths` initialization does not include it, so `_detect_changed_files` misses it entirely, returning an omitted representation.

#### Test 5: Tracking state after_paths initialization captures new context files (Output Channel)
- **Input:** A mocked agent creates a completely new file `context/new_shared.md`.
- **Expected:** Because `after_paths` initialization expands to include new allowed context files, it detects `context/new_shared.md`. The return tuple's `changed_files` list (Data Flow / Output Channel) contains it.
- **Actual (before fix):** `after_paths` initialization is hardcoded to prompt/code/tests, completely missing newly created shared files.

### Test Location
- **File:** `tests/test_agentic_update.py` (append — preferred)
- **Framework:** pytest

### Notes
To test `_revert_out_of_scope_changes` within `run_agentic_update`, the test fixtures must initialize a `git` repository in `tmp_path` via `subprocess.run` (`git init`, `git add .`, `git commit`). Otherwise, the `_revert_out_of_scope_changes` guard silently skips the reversion logic. We will use mocks for `run_agentic_task` to simulate the LLM's filesystem mutations and return values.

---
*Proceeding to Step 9: Generate Test*
