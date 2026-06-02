# Issue Identification - Side-Effect Policy Enforcement (Capability Contracts)

## Iteration 2 Review Results

### 1. Code-Prompt Desync (Stale Modules)
Multiple code modules have not been synchronized with their corresponding prompt updates, resulting in missing features and broken registration.
- **`pdd/commands/__init__.py`**: Fails to register the new `policy` command group despite the requirement in `pdd/prompts/commands/__init___python.prompt`.
- **`pdd/contract_ir.py`**: Missing the `extract_capabilities` function required by `pdd/prompts/contract_ir_python.prompt`.
- **`pdd/drift_main.py`**: While it attempts to import `run_policy_check`, the dependency `pdd/policy_check.py` is missing from disk.

### 2. Missing Deliverables
The following files are registered in `architecture.json` and have defined prompts but are missing from the filesystem:
- `pdd/policy_check.py` (generated from `pdd/prompts/policy_check_python.prompt`)
- `pdd/commands/policy.py` (generated from `pdd/prompts/commands/policy_python.prompt`)
This confirms that `pdd sync` was not successfully executed for these new modules.

### 3. Incorrect Include Paths in Prompts
Several prompts use invalid relative paths for `<include>` directives, likely due to a misunderstanding of the directory structure (`pdd/prompts/` is the prompt location, while code is in `pdd/`).
- **`pdd/prompts/checkup_gates_python.prompt`**: Uses `../pdd/checkup_review_loop.py`. Since the prompt is in `pdd/prompts/`, `..` resolves to `pdd/`. Thus, it is looking for `pdd/pdd/checkup_review_loop.py`, which does not exist. It should be `../checkup_review_loop.py`.
- **`pdd/prompts/checkup_review_loop_python.prompt`**: Uses `../pdd/list_drift_detection.py`. Should be `../list_drift_detection.py`.

### 4. Prompt Specification Gaps & Inconsistencies
- **Interface Mismatch (`contract_ir_python.prompt`)**: The `pdd-interface` only exposes `parse_prompt_contracts` and `extract_capabilities`, but the `Requirements` section lists multiple other essential functions (`extract_sections`, `extract_rules`, etc.). This risks incomplete code generation or broken dependencies for other modules.
- **Vague `PolicyResult` (`policy_check_python.prompt`)**: The prompt fails to specify fields for the `PolicyResult` dataclass. Specifically, `pdd/drift_main.py` requires a `passed: bool` attribute which is not guaranteed by the current prompt.
- **Bootstrapping Dependency (`commands/policy_python.prompt`)**: The prompt includes `pdd/policy_check.py` as a code dependency. This causes a circular failure if `policy_check.py` hasn't been generated yet. It should ideally include the `pdd-interface` from the prompt file instead.
- **Modal Verb Narrowing**: Both `contract_ir_python.prompt` and `policy_check_python.prompt` explicitly mention `MUST NOT` for setting `is_must_not=True`, but omit `SHALL NOT` and `MAY NOT`, which are currently handled by the existing (but stale) `contract_ir.py`.
- **Missing `Rule` class in `contract_ir_python.prompt`**: The prompt defines `Capability` but does not explicitly require the `Rule` dataclass (used for `<contract_rules>`), which may lead to its removal during regeneration.

### 5. Recommendation
The next step must focus on:
1. Correcting the include paths in the prompt files.
2. Expanding the `pdd-interface` and `Requirements` to ensure all necessary dataclasses (like `Rule`) and functions are preserved.
3. Defining the explicit structure of `PolicyResult` (including `passed: bool`).
4. Running a full `pdd sync` for all affected modules to restore the filesystem state and verify integration.
