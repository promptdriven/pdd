(This is still a draft).

Previously, `<include>` would insert an entire file into the prompt. Now you can use the `query` and `select` attributes with the `<include>` tag to extract specific parts of files instead of including the entire contents. Also, `auto-deps` will automatically insert the right selectors when it detects and inserts `<include>` tags in your prompt files. `select` is a deterministic attribute that will insert a specific function or heading. `query` uses LLM-powered semantic extraction of a file, and caches it in `.pdd/extracts/`.

### Canonical `<include>` Tag Format

The file path is always the **body content** of the tag. Optional attributes (`select`, `query`, `mode`) go on the opening tag:

```xml
<include>path/to/file</include>                                    <!-- full file -->
<include select="def:foo,class:Bar">path/to/file</include>        <!-- structural selector -->
<include query="...">path/to/file</include>                        <!-- semantic query -->
<include select="class:Handler" mode="interface">api.py</include>  <!-- interface mode -->
```

The file path is always the tag body.

### Structural Selectors (`select=`)

Extract file fragments by structure using `<include select="...">file</include>`

| Selector | Description | Example |
| -- | -- | -- |
| `lines:N-M` | Line ranges (single, range, open-ended) | `lines:10-20`, `lines:5-`, `lines:-3` |
| `def:name` | Python function/async function by name | `def:process_request` |
| `class:Name` | Entire Python class | `class:UserModel` |
| `class:Name.method` | Specific method from a class | `class:UserModel.validate` |
| `section:Heading` | Markdown section by heading text | `section:Installation` |
| `pattern:/regex/` | Lines matching a regex | `pattern:/^import/` |
| `path:key.nested[0]` | JSON/YAML value by dot-notation path | `path:config.database.host` |

Selectors are composable: `select="lines:1-5,def:main,def:helper"`

### Interface Mode (`mode="interface"`)

Extract only signatures, docstrings, and type hints — no implementation bodies:

```xml
<include select="class:Handler" mode="interface">api.py</include>
```

### Semantic Extraction (`query=`)

Use an LLM to extract relevant content based on a natural language query:

```xml
<include query="List all authentication requirements">spec.md</include>
```

Results are cached in `.pdd/extracts/` (keyed by `sha256(path + query)`), committed to git for reproducible builds, and invalidated when the source file changes.

### Cache Management (`pdd extracts prune`)

New CLI command to garbage-collect orphaned cache entries no longer referenced by any prompt file.

### Automatic Selector Insertion via Auto-Deps

Auto-deps (`pdd auto-deps` / `insert_includes`) now automatically determines *what parts* of each dependency are needed:

1. **Better summaries** — `summarize_file_LLM.prompt` produces structured output (`file_summary`, `key_exports`, `dependencies`) instead of prose. This gives auto-deps richer data for both file selection and selector emission.

2. **Selector-aware auto-include** — `auto_include_LLM.prompt` now understands selector types and emits `select=` or `query=` alongside file paths. It prefers structural selectors (deterministic, stays up-to-date) over semantic queries. The LLM returns structured JSON via Pydantic (`AutoIncludeResult`) with `new_includes` and `existing_include_annotations`.

3. **Deterministic `<update>` application** — When auto-deps annotates existing `<include>` tags with selectors, the replacement is applied deterministically via regex (no LLM call). The LLM is only invoked for inserting *new* includes.

4. **Small file optimization** — Files under 100 lines skip extraction entirely (the overhead exceeds the token savings).

5. **Single LLM call** — `extract_auto_include_LLM.prompt` has been removed. The old two-call pipeline (free-form LLM → extraction LLM) is replaced by a single call with Pydantic structured output.

---

## Changes

### New Modules

- **`pdd/content_selector.py`** — Selector parsing and extraction engine (lines, AST, markdown, regex, JSON/YAML path)
- **`pdd/include_query_extractor.py`** — LLM-powered semantic extraction with deterministic caching
- **`pdd/extracts_prune.py`** — Cache garbage collection logic
- **`pdd/commands/extracts.py`** — CLI registration for `pdd extracts prune`
- **`pdd/server/routes/extracts.py`** — REST API for browsing extracts cache

### Modified Modules

- **`pdd/preprocess.py`** — Wired `select`, `mode`, and `query` attributes into `<include>` tag processing
- **`pdd/auto_include.py`** — Single LLM call with `AutoIncludeResult` Pydantic model; emits `<new>`/`<update>` blocks with selectors; small-file stripping
- **`pdd/insert_includes.py`** — Deterministic `<update>` block application; LLM only handles `<new>` blocks
- **`pdd/summarize_directory.py`** — `FileSummary` Pydantic model gains `key_exports`/`dependencies`; CSV output has 5 columns; backward-compatible parsing of older CSV formats
- **`pdd/commands/__init__.py`** — Registered the `extracts` command group
- **`.gitignore`** — Excepted `.pdd/extracts/` so cache entries can be committed

### Prompts — New

| Prompt | Purpose |
|--------|---------|
| `pdd/prompts/content_selector_python.prompt` | `ContentSelector` class with structural extraction |
| `pdd/prompts/include_query_extractor_python.prompt` | `IncludeQueryExtractor` class with caching |
| `pdd/prompts/extracts_prune_python.prompt` | `pdd extracts prune` CLI subcommand |
| `pdd/prompts/server/routes/extracts_python.prompt` | REST API for browsing extracts cache |
| `pdd/prompts/include_query_extractor_LLM.prompt` | LLM instructions for semantic extraction |

### Prompts — Modified

| Prompt | Change |
|--------|--------|
| `pdd/prompts/auto_include_LLM.prompt` | **Rewritten.** Now selector-aware: documents selector types, guidelines for when to use `select` vs `query` vs full file, structured JSON output matching Pydantic models |
| `pdd/prompts/auto_include_python.prompt` | Single LLM call with `AutoIncludeResult`; `<new>`/`<update>` output format; `_strip_selectors_from_small_files`; no extract step |
| `pdd/prompts/summarize_file_LLM.prompt` | Structured output: `file_summary` (one sentence), `key_exports` (list), `dependencies` (list) |
| `pdd/prompts/summarize_directory_python.prompt` | `FileSummary` Pydantic model gains `key_exports`/`dependencies`; CSV has 5 columns; backward-compatible parsing |
| `pdd/prompts/insert_includes_python.prompt` | `<update>` blocks applied deterministically via `_apply_update_blocks()`; LLM only sees `<new>` blocks; skips LLM call if no new includes |
| `pdd/prompts/preprocess_python.prompt` | Tag syntax updated to canonical body-content format |

### Prompts — Removed

| Prompt | Reason |
|--------|--------|
| `pdd/prompts/extract_auto_include_LLM.prompt` | Eliminated second LLM call. Replaced by Pydantic structured output from `auto_include_LLM`;  |

### Documentation

- **`README.md`** — Tag syntax fixed to canonical format; `pdd extracts prune` docs
- **`docs/prompting_guide.md`** — Selective include syntax, selector reference, LLM extraction docs; all examples use canonical body-content format