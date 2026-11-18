# Repo hygiene and extensible project lint

Own `src/repo-hygiene-lint.mjs`. Export `lintRepoAntiPatterns({root, files, promptPaths, tests, config})`, `lintRepoProject({root, files, promptPaths, tests, config})`, `loadProjectLintConfig(rootOrObject)`, `stripPromptMetadata(raw)`, `isInspectableTestCodePath(path)`, `lintFakeTests(text, {path})`, `lintPublicInterfaceTests(text, {path})`, `lintPromptCodeBlocks(text, {path})`, `lintPromptSize(promptText, codeFiles, {path})`, and `lintPromptStructure(text, {path, hasOwnedCode})`. It reads local regular in-root files only, makes no AI or network call, writes no file, and emits deterministic sorted `"Warning: …"` lines by default (exit code 0 on `pdd lint --local`), while returning `errors` in `lintRepoProject` when `pdd.json` promotes a rule to `"severity": "error"`.

## Workspace scope and safety

Resolve `realRoot = realpathSync(root)`, default `files` to Git-visible repository-relative paths (`gitFiles(realRoot)`), filter out secret paths (`isSecretPath`) and paths outside the workspace policy (`workspace.policy({root: realRoot})`, `workspace.allows(policy, path)`), and skip nested `fixtures/` folders unless explicitly selected in `promptPaths` or `tests`. Open only regular in-root files without following symlinks and skip unreadable, escaping, symlinked or oversized candidates without throwing.

- **Prompts:** With `promptPaths`, inspect only those allowed `.prompt.md` paths; without `promptPaths`, inspect every scoped `.prompt.md`.
- **Stories:** When neither `promptPaths` nor `tests` scopes the run, inspect every scoped `isLintableStoryPath(path)` file. When `tests` or `promptPaths` scopes a Story run, inspect only lintable Stories matched by `tests` or referenced via `story_path` in scoped scenario JSON files whose `steps[].entry_path`, `entry_paths` or `context` intersect `promptPaths`.
- **Tests:** Inspect scoped code test files (`isTestOwnedPath(path)` with a code file extension, excluding `fixtures/`, `helpers/`, `.json` scenario files, and structural `*seam.test.*` boundary guards). When `promptPaths` is supplied, keep only test findings whose inspected target or owning prompt matches one of `promptPaths`.

## Built-in deterministic rules

| Rule IDs | Target | What fails the check |
| --- | --- | --- |
| `prompt-larger-than-code` | Prompt + owned code | Strip YAML frontmatter and `Runtime interface` blocks, resolve owned production code via `resolveOwners`, and warn when owned code exists and `promptLines >= codeLines` (requiring `prompt lines < code lines`). |
| `test-private-import`, `test-private-access` | `test/` code | Tokenize comments and string/template literals while keeping 1-based line numbers; warn on private implementation path imports (`/internal/`, `/_internal/`, `/private/`, `/_private/`, `/impl/`, or single-underscore files outside dunders), single-underscore symbol imports (`_helper`), `._member` access on imported production modules/instances, rewire hooks (`__get__`, `__set__`, `__Rewire__`, `__ResetDependency__`, `rewire(...)`), or `vm` evaluation of `src/` files. |
| `prompt-missing-title`, `prompt-missing-dependencies`, `prompt-missing-diagram` | Prompt | Missing `# <Title>`; missing `## Dependencies` on module/interface/peer-linking/multi-section prompts; or multi-state transitions (`>= 3` transition lines) or dense branching (`>= 5` branching clauses across `>= 18` prose lines) with no `mermaid` diagram, linked `.ui.svg`, or Markdown table. |
| `fake-test-prompt-read`, `fake-test-exists-check`, `fake-test-source-match` | `test/` code | Reading `.prompt.md` prose directly, checking file existence on `prompts/` or `src/`, or matching raw `src/` source strings instead of exercising module exports or CLI commands. |
| `prompt-code-fence-length`, `prompt-code-fence-total`, `prompt-imperative-code` | Prompt | Non-`mermaid` / non-`pdd-boundary` non-JSON code fences exceeding `15` lines (`30` total) or containing imperative code statements. |
| `story-*` | Story | `lintStory(text, {path, criteriaHygiene: true})` criteria and length checks. |

## Extensible project rules (`pdd.json`)

Load root `pdd.json` `"lint"` settings via `loadProjectLintConfig`:
- `disable`: array of rule IDs turned off.
- `rules`: object mapping rule IDs to `"off" | "warn" | "error"` (or `{severity}`).
- `custom_rules`: array of declarative project rules `{id, target, include, exclude, severity, forbid_pattern, require_pattern, require_heading, max_lines, flags, message}` scoped to `"prompt" | "story" | "test" | "code" | "all"`. Collapse redundant `*` / `**` glob segments, reject globs exceeding `12` wildcards, and reject unsafe regular expressions (backreferences, nested quantifiers, ambiguous repeated alternations, or lookarounds containing unbounded quantifiers) or malformed `lint` entries as `[lint-config-invalid]` without throwing.

## Dependencies

- [Story quality lint](story-lint.prompt.md): required generation context for `isLintableStoryPath` and `lintStory`.
- [File owner lookup](file-owner.prompt.md): required generation context for `isTestOwnedPath` and `resolveOwners`.
- [PDD to Runtime seam](runtime-seam.prompt.md): required generation context for `gitFiles`, `isSecretPath` and `workspace`.
