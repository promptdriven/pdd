<!-- pdd-story-prompts: commands/context_python.prompt -->

# User Story: Audit context-window usage by source

<!--
Issue-derived story (issue #1356 workflow). Authored from GitHub issue #789
("Context optimization: add context budget audit command") plus the intentional
change tracked in PR #1387 (command renamed to `pdd context`; default output is a
Claude-Code /context-style usage box). This story is the behavioral source of
truth and is deliberately independent of `commands/context_python.prompt`: it
describes WHAT a context audit must show, not HOW the command is implemented, so
it can fail when the prompt drifts away from the issue's intent.

Regeneration path (needs a keyed env):
  pdd test --issue 789 prompts/commands/context_python.prompt
-->

## Covers

- AC1: Reports total hydrated tokens and percent of the selected model's context window.
- AC2: Breaks tokens down per source (prompt body, each include, grounding, ...).
- AC3: Shows the largest token consumers first.
- AC4: Supports JSON output for CI and dashboards.
- AC5: Makes no LLM call for the deterministic portions of the audit.
- AC6: Surfaces deferred/nondeterministic tags with clear warnings.
- AC7: Per-include attribution reflects what is actually hydrated — a targeted include
  (`lines=`, `select=`, `mode=`, `<include-many>`) is counted by its realized content,
  not the whole source file — so no row exceeds the prompt's own total. Independent
  top-level includes are not dropped just because their realized text overlaps.
- AC8: Unresolved/missing includes are surfaced (warning + row), never silently hidden,
  while code-fenced examples and optional missing includes follow preprocess semantics.
- CH1 (PR #1387 intentional change): default output is a Claude-Code `/context`-style
  usage box under the `pdd context` command name; the raw attribution table is available
  via `--table`.

## Story

As a PDD developer optimizing context usage,
I can run `pdd context <prompt>` to see how much of the model's context window a
hydrated prompt consumes, broken down by source and rendered like Claude Code's
`/context` display,
so that I can find the largest context consumers and gate CI on a token budget
without spending an LLM call.

## Context

`commands/context_python.prompt` defines the `pdd context <prompt_path>` command.
It preprocesses the prompt the same way generation does, counts tokens per source
segment, and renders the result. The model's context limit comes from
`pdd.server.token_counter.get_context_limit`; token counts come from
`count_tokens`; dynamic-tag detection comes from `pdd.context_snapshot.detect_dynamic_tags`.
Grounding requires PDD Cloud and is reported as 0 tokens with a warning rather
than triggering a network call.

## Acceptance Criteria

1. Given a prompt with one or more `<include>` directives, when I run `pdd context <prompt>`,
   then the default output is a usage box headed `Context Usage` that names the model,
   reports `total/limit tokens (percent%)`, and lists usage by category — one line per
   source — not only an aggregate total.
2. Given the same prompt, when I run `pdd context <prompt> --table`, then I get the
   per-source attribution table with `Source`, `Tokens`, and `% of total` columns, and
   the rows are ordered largest-token-consumer first.
3. Given `--json`, when the audit completes, then stdout is a single JSON object with
   keys `total_tokens`, `context_limit`, `percent_used`, `model`, `rows`, `warnings`,
   and `threshold_exceeded`, with `rows` sorted by `tokens` descending.
4. Given the hydrated prompt exceeds `--threshold` percent of the context limit, when a
   nonzero threshold is set, then the command exits with code 2; given `--threshold 0`,
   then the check is disabled and the command exits 0.
5. Given a prompt containing dynamic tags such as `<shell>` or `<web>` — in the prompt
   itself or inside an included file — when they are not expanded, then a warning is
   reported for each, the deferred tag markup is excluded from the token total, and no
   LLM/network call is made.
6. Given an include that targets part of a file (`lines=`/`select=`/`mode=`) or a literal
   `<include-many>` list, when I run `pdd context <prompt>`, then each include is attributed
   by its realized (post-selection) content and no row's tokens exceed `total_tokens`.
7. Given two independent top-level includes whose contents overlap, when I run
   `pdd context <prompt>`, then both top-level include rows appear and are not mistaken for
   a nested include relationship.
8. Given an include whose path does not resolve to a readable file (and is not a deferred
   `${VAR}` path), when I run `pdd context <prompt>`, then it appears as a warning and as a
   `0`-token row marked unresolved, rather than being folded into the prompt body.
9. Given include or include-many syntax inside a fenced/inline code example, when I run
   `pdd context <prompt>`, then it is treated as documentation, not expanded or reported
   unresolved; given a static optional missing include, then it is skipped silently.

## Oracle

These details matter for pass/fail:
- A per-source breakdown is present (prompt body and each resolved include); aggregate-only
  totals are not sufficient.
- The default (no-flag) output is the `/context`-style usage box, and `--table` produces the
  attribution table.
- Rows are sorted by token count descending.
- JSON contains exactly the documented keys; `threshold_exceeded` drives exit code 2.
- No LLM call is made for the deterministic audit.
- Each unexpanded dynamic tag produces a warning.
- Top-level include identity comes from the expansion path, not string containment.
- Missing include warnings mirror preprocess code-span and optional semantics.

## Non-Oracle

These details should not matter:
- The exact glyphs used in the usage box and the grid dimensions.
- Private helper names and internal module structure.
- Table column padding/styling.
- Ordering of rows that have equal token counts.

## Negative Cases

- Reporting only an aggregate token total with no per-source attribution.
- Dropping the per-source breakdown when rendering the `/context`-style box.
- Making an LLM or network call during a deterministic audit.
- Silently ignoring `<shell>`/`<web>` dynamic tags instead of warning.
- Failing to exit non-zero when the budget threshold is exceeded.
- Counting a whole include file when the include only selects part of it (a row whose
  token count exceeds the prompt total).
- Dropping an independent top-level include because its content is contained in another
  top-level include's content.
- Reporting unresolved rows for include syntax inside fenced/inline code examples.
- Warning on static optional missing includes.
- Counting deferred dynamic-tag markup (`<shell>`/`<web>`/`query=`) as hydrated payload.
- Silently folding an unresolved/missing include into the prompt body.

## Non-Goals

- Generating code from the audited prompt.
- Fetching cloud grounding data locally.
- Replacing the Claude Code `/context` command itself.

## Notes

- This story must fail validation if the prompt changes from per-source attribution to
  aggregate-only totals, or removes the default `/context`-style usage box, or introduces
  an LLM call into the deterministic path.
- Tests in `tests/commands/test_context.py` encode each acceptance criterion above; the
  AC each test maps to is named in the test docstring.
