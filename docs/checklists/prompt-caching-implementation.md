# Prompt Caching Implementation — Checklist

This document tracks the implementation of prompt caching for Vertex AI models (Claude Opus 4.5 and Gemini 3 Pro) to reduce LLM costs by up to 90%.

## Problem Summary

pdd currently has response caching (caches complete API responses) but lacks **prompt caching** (provider-side caching of prompt prefixes). This means:

| Model | Current State | Potential Savings |
|-------|---------------|-------------------|
| Claude Opus 4.5 | No caching benefits | **90% on cached tokens** |
| Gemini 3 Pro | Implicit caching (automatic) | Already benefiting |

**Goal:** Enable explicit prompt caching for Claude Opus 4.5 via litellm's `cache_control_injection_points` parameter.

---

## Model-Specific Details

### Claude Opus 4.5 (via Vertex AI)

| Feature | Details |
|---------|---------|
| **Caching Type** | Explicit only - requires `cache_control` markers |
| **Minimum Tokens** | 4,096 tokens |
| **Cache Read Cost** | $0.50/M tokens (vs $5/M base = 90% savings) |
| **5-min Cache Write** | $6.25/M tokens (1.25× base) |
| **1-hour Cache Write** | $10/M tokens (2× base) |
| **TTL Options** | 5 minutes (default) or 1 hour |
| **Max Breakpoints** | 4 per request |

### Gemini 3 Pro (via Vertex AI)

| Feature | Details |
|---------|---------|
| **Caching Type** | **Implicit (automatic)** + Explicit option |
| **Minimum Tokens** | 2,048 tokens |
| **Cache Discount** | 90% discount on cached tokens |
| **Default State** | **Already enabled** - no code changes required |
| **TTL** | Minimum 1 minute, no maximum |

---

## Expected Results

| Scenario | Current Cost | After Implementation |
|----------|--------------|---------------------|
| Claude Opus 4.5: 10K system prompt, repeated 10× | $0.50 | ~$0.10 (after first call) |
| Gemini 3 Pro | Already optimized | No change needed |

---

## Implementation Order

Execute changes in this order to minimize risk and allow incremental testing:

1. Add cache control injection for Vertex AI Claude models
2. Update callback to track cached tokens
3. Expose cached tokens in return value
4. Add verbose logging for cache metrics
5. Update llm_model.csv with caching metadata (optional)

Run `pytest -vv tests/test_llm_invoke.py` after each step.

---

## Checklist

### Phase 1: Core Implementation

- [ ] **1.1 Add cache_control_injection_points for Claude models**
  - [ ] Locate the `litellm.completion()` call in `llm_invoke.py` (~line 1734)
  - [ ] Add condition to detect Vertex AI Claude models:
    ```python
    is_vertex_claude = (
        model_name_litellm.startswith('vertex_ai/') and
        'claude' in model_name_litellm.lower()
    )
    ```
  - [ ] Add cache control injection before completion call:
    ```python
    if is_vertex_claude:
        litellm_kwargs["cache_control_injection_points"] = [
            {"location": "message", "role": "system"}
        ]
    ```
  - [ ] Run `pytest tests/test_llm_invoke.py`
  - [ ] Verify: Test with Claude model and check for `cache_control` in debug logs

- [ ] **1.2 Update _LAST_CALLBACK_DATA for cache metrics**
  - [ ] Add new fields to `_LAST_CALLBACK_DATA` dict (line ~390):
    ```python
    _LAST_CALLBACK_DATA = {
        "input_tokens": 0,
        "output_tokens": 0,
        "finish_reason": None,
        "cost": 0.0,
        "cached_tokens": 0,           # NEW
        "cache_creation_tokens": 0,   # NEW
    }
    ```
  - [ ] Update `_litellm_success_callback()` to extract cache metrics:
    ```python
    # After existing usage extraction
    cached_tokens = getattr(usage, 'cached_tokens', 0) or \
                    getattr(usage, 'cache_read_input_tokens', 0)
    cache_creation = getattr(usage, 'cache_creation_input_tokens', 0)

    _LAST_CALLBACK_DATA["cached_tokens"] = cached_tokens
    _LAST_CALLBACK_DATA["cache_creation_tokens"] = cache_creation
    ```
  - [ ] Run `pytest tests/test_llm_invoke.py`

- [ ] **1.3 Expose cached tokens in return value**
  - [ ] Update the return dictionary in `llm_invoke()` (~line 1850+):
    ```python
    return {
        'result': final_result,
        'cost': total_cost,
        'model_name': model_name_litellm,
        'thinking_output': thinking_output,
        'cached_tokens': _LAST_CALLBACK_DATA.get("cached_tokens", 0),
        'cache_creation_tokens': _LAST_CALLBACK_DATA.get("cache_creation_tokens", 0),
    }
    ```
  - [ ] Run `pytest tests/test_llm_invoke.py`

### Phase 2: Observability

- [ ] **2.1 Add verbose logging for cache metrics**
  - [ ] In the verbose output section (~line 1738), add:
    ```python
    if verbose and _LAST_CALLBACK_DATA.get("cached_tokens", 0) > 0:
        logger.info(f"[CACHE] Tokens read from cache: {_LAST_CALLBACK_DATA['cached_tokens']}")
    if verbose and _LAST_CALLBACK_DATA.get("cache_creation_tokens", 0) > 0:
        logger.info(f"[CACHE] Tokens written to cache: {_LAST_CALLBACK_DATA['cache_creation_tokens']}")
    ```
  - [ ] Run manual test with `verbose=True` and Claude model

- [ ] **2.2 Add cache hit rate calculation (optional)**
  - [ ] Add helper to calculate savings:
    ```python
    def _calculate_cache_savings(cached: int, created: int, total: int) -> float:
        """Calculate percentage of tokens served from cache."""
        if total == 0:
            return 0.0
        return (cached / total) * 100
    ```
  - [ ] Log cache hit rate in verbose mode

### Phase 3: Configuration (Optional)

- [ ] **3.1 Add prompt_caching column to llm_model.csv**
  - [ ] Add column `prompt_caching` with values: `auto`, `explicit`, `none`
  - [ ] Update Claude models: `prompt_caching=explicit`
  - [ ] Update Gemini models: `prompt_caching=auto`
  - [ ] Update OpenAI models: `prompt_caching=auto` (≥1024 tokens)
  - [ ] Update other models: `prompt_caching=none`

- [ ] **3.2 Add enable_prompt_caching parameter (optional)**
  - [ ] Add parameter to `llm_invoke()` signature:
    ```python
    def llm_invoke(
        ...,
        enable_prompt_caching: bool = True,
    ) -> Dict[str, Any]:
    ```
  - [ ] Wrap cache control injection in conditional:
    ```python
    if enable_prompt_caching and is_vertex_claude:
        litellm_kwargs["cache_control_injection_points"] = [...]
    ```
  - [ ] Update docstring

- [ ] **3.3 Add TTL configuration (optional)**
  - [ ] Add `PDD_CACHE_TTL` env var support (values: `5m`, `1h`)
  - [ ] Map to cache_control format:
    ```python
    ttl = os.getenv("PDD_CACHE_TTL", "5m")
    cache_control = {"type": "ephemeral"}
    if ttl == "1h":
        cache_control["ttl"] = "1h"
    ```

### Validation

- [ ] **Final testing**
  - [ ] Test with Claude Opus 4.5: verify `cached_tokens > 0` on second call
  - [ ] Test with Gemini 3 Pro: verify no errors (implicit caching continues)
  - [ ] Test with OpenAI models: verify no changes to behavior
  - [ ] Run full test suite: `pytest -vv tests/`
  - [ ] Run regression tests: `make regression`

- [ ] **Cost verification**
  - [ ] Make two identical Claude calls with large system prompt (>4096 tokens)
  - [ ] Verify second call shows `cached_tokens` in response
  - [ ] Verify cost is reduced on second call

- [ ] **Documentation**
  - [ ] Update CHANGELOG with prompt caching feature
  - [ ] Document new return fields: `cached_tokens`, `cache_creation_tokens`
  - [ ] Document env vars: `PDD_CACHE_TTL` (if implemented)

---

## Critical Files

| File | Changes |
|------|---------|
| `pdd/llm_invoke.py` | Add cache_control_injection_points, update callback, expose metrics |
| `data/llm_model.csv` | (Optional) Add prompt_caching column |
| `tests/test_llm_invoke.py` | Add tests for cache metrics |

---

## Code Locations

| Component | File | Line Numbers |
|-----------|------|--------------|
| litellm.completion() call | `pdd/llm_invoke.py` | ~1734 |
| _LAST_CALLBACK_DATA | `pdd/llm_invoke.py` | ~390-396 |
| _litellm_success_callback | `pdd/llm_invoke.py` | ~397-476 |
| Return dictionary | `pdd/llm_invoke.py` | ~1850+ |
| Verbose logging | `pdd/llm_invoke.py` | ~1738 |

---

## Rollback Controls

Environment variables for disabling optimizations:
- `LITELLM_CACHE_DISABLE=1` - Disable response cache (existing)
- `PDD_PROMPT_CACHING=false` - Disable prompt caching (new, if implemented)

---

## Risk Mitigation

- Run tests after each step to catch regressions early
- Gemini implicit caching continues working regardless of changes
- Claude-specific changes are isolated behind model detection
- All changes are additive (new return fields) - backward compatible

---

## Sources

- [LiteLLM Prompt Caching](https://docs.litellm.ai/docs/completion/prompt_caching)
- [LiteLLM Auto-Inject Caching](https://docs.litellm.ai/docs/tutorials/prompt_caching)
- [Claude Prompt Caching Docs](https://platform.claude.com/docs/en/build-with-claude/prompt-caching)
- [Vertex AI Context Caching](https://docs.cloud.google.com/vertex-ai/generative-ai/docs/context-cache/context-cache-overview)
- [Claude Opus 4.5 on Vertex AI](https://cloud.google.com/blog/products/ai-machine-learning/claude-opus-4-5-on-vertex-ai)
