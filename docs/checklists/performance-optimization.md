# PDD Performance Optimization — Checklist

This document tracks the implementation of performance optimizations to reduce PDD CLI cold-start time from ~1.5s to ~0.3-0.4s.

## Problem Summary

Profiling revealed `pdd generate` has significant performance overhead:

| Component | Time | % of Cold Start |
|-----------|------|-----------------|
| Module imports | ~1.1s | 71% |
| LLM API calls | ~12-23s | Variable (network) |
| Auto-update check | ~200ms | 13% |
| Git operations | ~160ms | 10% |
| LiteLLM cache ops | ~940ms | Network I/O |

**Goal:** Reduce cold-start time from ~1.5s to ~0.3-0.4s for non-LLM commands (e.g., `--help`, `--version`)

---

## Expected Results

| Scenario | Current | After Phase 1 | After Phase 2 |
|----------|---------|---------------|---------------|
| `pdd --help` | ~1.5s | ~1.1s | ~0.3-0.4s |
| `pdd --version` | ~1.5s | ~1.1s | ~0.3-0.4s |
| `pdd generate` (cached) | ~1.5s | ~1.1s | ~0.5s + LLM |
| Tab completion | ~1.5s | ~1.1s | ~0.3s |

---

## Implementation Order

Execute changes in this order to minimize risk and allow incremental testing:

1. `pdd/get_extension.py` - Replace pandas with csv (isolated, easy to test)
2. `pdd/auto_update.py` - Add TTL caching (isolated, improves every run)
3. `pdd/auto_include.py` - Replace pandas with csv (isolated)
4. `pdd/llm_invoke.py` - Lazy litellm import + lazy cache init
5. `pdd/llm_invoke.py` - Replace pandas with list-of-dicts helpers
6. `pdd/llm_invoke.py` - Add Vertex credentials caching
7. `pdd/core/cli.py` - Lazy auto_update import
8. `pdd/cli.py` - Lazy re-exports with `__getattr__`
9. `pdd/code_generator_main.py` - Git operations caching
10. `pdd/preprocess.py` + `pdd/code_generator_main.py` - Consolidate preprocessing

Run `pytest -vv tests/` and `time pdd --help` after each step.

---

## Checklist

### Phase 1: Quick Wins

- [ ] **1.1 Replace pandas in get_extension.py** (~155ms)
  - [ ] Replace `import pandas as pd` with `import csv`
  - [ ] Rewrite `get_extension()` to use `csv.DictReader`
  - [ ] Run `pytest tests/test_get_extension.py`
  - [ ] Verify: `time pdd --help`

- [ ] **1.2 Auto-update TTL cache** (~200ms on 95% of runs)
  - [ ] Add `_load_update_cache()` function
  - [ ] Add `_save_update_cache()` function
  - [ ] Add `_is_cache_valid(ttl_hours=24)` function
  - [ ] Modify `auto_update()` to check cache before HTTP request
  - [ ] Add `PDD_UPDATE_TTL_HOURS` env var support
  - [ ] Test: run `pdd --help` twice, second should skip PyPI check

- [ ] **1.3 Lazy LiteLLM cache init** (~200ms)
  - [ ] Move cache configuration (lines 306-385) into `_ensure_cache_initialized()` function
  - [ ] Add `_cache_initialized` module-level flag
  - [ ] Call `_ensure_cache_initialized()` at start of `llm_invoke()`
  - [ ] Verify: `pdd --help` should not log "LiteLLM cache configured"

### Phase 2: Import Optimization

- [ ] **2.1 Lazy litellm import** (~686ms)
  - [ ] Remove top-level `import litellm`
  - [ ] Add `_lazy_modules = {}` dict
  - [ ] Add `_get_litellm()` lazy accessor function
  - [ ] Replace all `litellm.X` with `_get_litellm().X`
  - [ ] Move litellm configuration into `_get_litellm()`
  - [ ] Run full test suite

- [ ] **2.2 Lazy auto_update import**
  - [ ] Move `from ..auto_update import auto_update` inside conditional block in `core/cli.py`
  - [ ] Verify tests pass

- [ ] **2.3 Replace pandas in llm_invoke.py**
  - [ ] Add helper functions: `_safe_float()`, `_safe_int()`, `_safe_bool()`
  - [ ] Rewrite `_load_model_data()` to use `csv.DictReader` returning `List[Dict]`
  - [ ] Rewrite `_select_model_candidates()` to work with list-of-dicts
  - [ ] Rewrite `_set_model_rate_map()` to work with list-of-dicts
  - [ ] Remove pandas import and configuration
  - [ ] Update test mocks to use list-of-dicts instead of DataFrames
  - [ ] Run `pytest tests/test_llm_invoke.py`

### Phase 3: Runtime Optimization

- [ ] **3.1 Git operations caching** (~140ms)
  - [ ] Create `_git_cache` dict for session-level caching
  - [ ] Cache `is_git_repository()` results by path
  - [ ] Cache `rev-parse --show-toplevel` results
  - [ ] Add cache reset at CLI entry point
  - [ ] Verify generate command still works correctly

- [ ] **3.2 Vertex credentials caching** (~160ms)
  - [ ] Add `_VERTEX_CREDENTIALS_CACHE` module-level dict
  - [ ] Add `_get_cached_vertex_credentials()` function with mtime validation
  - [ ] Replace inline credential loading in `llm_invoke()`
  - [ ] Test with Vertex AI model

- [ ] **3.3 Consolidated preprocessing** (~50-100ms)
  - [ ] Add `preprocess_full()` single-pass function to `preprocess.py`
  - [ ] Update `code_generator_main.py` to use single preprocess call
  - [ ] Verify "Starting prompt preprocessing" appears only once
  - [ ] Run regression tests

### Phase 4: Architectural Cleanup

- [ ] **4.1 Lazy CLI re-exports**
  - [ ] Create `_LAZY_EXPORTS` mapping dict in `cli.py`
  - [ ] Implement `__getattr__()` for lazy module loading
  - [ ] Remove eager imports (lines 17-39)
  - [ ] Test: `from pdd.cli import code_generator_main` still works
  - [ ] Run full test suite

- [ ] **4.2 Replace pandas in auto_include.py**
  - [ ] Replace `pd.read_csv(StringIO())` with `csv.DictReader()`
  - [ ] Update list comprehension to replace `.apply()`
  - [ ] Test auto-include functionality

### Validation

- [ ] **Final benchmarks**
  - [ ] Record: `time pdd --help` (target: <0.4s)
  - [ ] Record: `time pdd --version` (target: <0.3s)
  - [ ] Record: `time pdd generate --help` (target: <0.4s)
  - [ ] Record: `python -X importtime -c "from pdd.cli import cli" 2>&1 | head -5`

- [ ] **Full test suite**
  - [ ] `pytest -vv tests/`
  - [ ] `make regression`

- [ ] **Documentation**
  - [ ] Update CHANGELOG with performance improvements
  - [ ] Document new env vars: `PDD_UPDATE_TTL_HOURS`

---

## Critical Files

1. **`pdd/get_extension.py`** - Replace pandas with csv module
2. **`pdd/auto_update.py`** - Add TTL-based caching
3. **`pdd/auto_include.py`** - Replace pandas with csv module
4. **`pdd/llm_invoke.py`** - Lazy imports, replace pandas, credentials caching
5. **`pdd/core/cli.py`** - Lazy auto_update import
6. **`pdd/cli.py`** - Lazy re-exports with `__getattr__`
7. **`pdd/code_generator_main.py`** - Git caching, preprocessing consolidation
8. **`pdd/preprocess.py`** - Add single-pass preprocessing function

---

## Rollback Controls

Environment variables for disabling optimizations:
- `PDD_AUTO_UPDATE=false` - Skip update check (existing)
- `PDD_UPDATE_TTL_HOURS=0` - Force fresh check (new)
- `LITELLM_CACHE_DISABLE=1` - Disable LLM cache (existing)

---

## Risk Mitigation

- Run tests after each step to catch regressions early
- Keep environment variable rollbacks available
- Test backward compatibility for `from pdd.cli import X` imports
