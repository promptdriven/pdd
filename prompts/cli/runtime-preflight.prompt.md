# Runtime preflight

Own `src/runtime-preflight.mjs`. It does all local work for `pdd check` and `pdd try` before anything goes to the PDD runtime: it finds the files, the tests and the stories, checks each test, computes the prose hash, fills draft hashes and builds the source tar. It makes no network call and never reads a token.

## Files

- Git files = `git ls-files -z -co --exclude-standard` in the repo root, unique and sorted. A deleted tracked file is skipped.
- A test is a Git-visible `*.json` file of at most 1 MiB with the top-level `schema_version` `prompt-runtime.program-scenario.v1`. A `*.json` file that names `prompt-runtime.program-scenario` but is not valid JSON, or names another version, is a test that fails rule P1.
- A story is a Git-visible `*.md` file in a `user_stories` folder. Its name is the file name without `.md`. Its title is its first `# ` line. A story with no test gives a warning.
- Select tests by STORY words: a test path, a story path, a story name or a test file name without `.json`. No word selects every test. An unknown word is a command error that lists the stories with tests.

## Rules (engine 7b03d3ea codes; `pdd-*` codes are pdd only)

A story may have more than one test file (for example a different starting world). Each file must still cover every criterion of its story (P5, P6). There is no P11.

Check each selected test. Stop at the first broken rule; that test is refused and is not sent.

| # | Rule | Code |
|---|---|---|
| P1 | Valid JSON; only the engine's top-level keys; `schema_version` is v1 | `invalid-document` |
| P2 | `story_path` is set and names a Git-visible file | `pdd-no-story`, `story-missing` |
| P3 | No `criteria_scope`; `check_exemptions` absent or empty | `pdd-partial-test` |
| P4 | The story has criteria | `story-criteria-missing` |
| P5 | Test criterion texts equal the story items (sorted). Name the first missing or extra line | `story-criterion-mismatch` |
| P6 | Unique IDs; each ID has a check and an exact check (the engine's exact predicate) | `duplicate-criterion`, `unchecked-criteria`, `criterion-needs-exact-check` |
| P7 | `entry_path` is a Git-visible `*.prompt.md` with one interface block, `approved` or `draft`, hash current | `entry-missing`, `interface-missing`, `pdd-two-interfaces`, `invalid-json`, `interface-unapproved`, `interface-stale` |
| P8 | `operation` is in the interface `entries` | `entry-operation-missing` |
| P9 | `input` matches `input_schema`. Skip an input that holds `$step_result`. Report every problem of every step at once | `invalid-input` |
| P10 | An error step's `expected_error` is in the entry `errors`, with one `equals` check on `error` `/code` | `pdd-unknown-error`, `missing-error-check` |

A broken step or check shape uses the engine code (`missing-steps`, `invalid-step`, `invalid-check`, `unknown-criterion`, `invalid-criterion`). A step may name a `model` (as the live engine eae2202a allows); a model that is not a nonblank string is `invalid-step-model`. pdd is never stricter than the live engine.
- Default `max_calls` for a test: 4 for each step, at least 6, at most 100 (steps with saved data or prompt calls cost 2 to 3 AI calls each). A refusal has `code`, `section` (engine style, for example `steps[0].input.items[0].quantity`), `message`, an optional `hint` and the 1-based `step`.

- P7: drafts may run (Serhan, Oct 27). A `draft` with a current hash passes, and its row is marked `draft`. A status that is neither `draft` nor `approved` is `interface-unapproved`. Stale hints: approved = `pdd: the text changed after approval: set status to draft, run pdd check --fill-hash, ask the person.`; draft = `pdd: <path> is a draft whose text changed after its hash was filled. Run pdd check --fill-hash.` Preflight never sets `approved`; only [pdd approve](prompt-approve.prompt.md) does, after a person's `y` in a terminal.
- Schema rules (after P7, for the entry prompt and the prompts it calls; real-user web test, issue 1): check the engine's executable schema subset (`graph_runtime_protocol.py` `_validate_schema_node`, eae2202a) on every `entries[].input_schema` and `result_schema` (any root type) and every `resources[].operations[].arguments_schema` and `result_schema` (an object root). Report ALL problems at once, each with the engine code, the JSON pointer into the interface (`/entries/0/input_schema/properties/read`) and the rule in words:
  - a schema is a nonempty object; a `type` list is `graph-schema-type-list` (use `oneOf`); `$ref`, `$dynamicRef`, `anyOf`, `allOf`, `not`, `if`, `then`, `else`, `contains`, `unevaluatedProperties`, `patternProperties`, `propertyNames`, `contentEncoding` are `graph-schema-unsupported-keyword`;
  - `oneOf` stands alone (only annotations beside it), is a nonempty list with no repeated schema, and each variant follows these rules;
  - `type` is null, boolean, string, integer, number, array or object (`graph-schema-type-invalid`), with only its own keywords: null/boolean `enum`, `const`; string also `minLength`, `maxLength`, `pattern`; integer/number also `minimum`, `maximum`, `exclusiveMinimum`, `exclusiveMaximum`, `multipleOf`; array `items` (required), `enum`, `const`, `minItems`, `maxItems`, `uniqueItems`; object `properties`, `required` (a list of property names; it may be empty, and a name not in it is optional), `additionalProperties` (must be `false`: `graph-schema-open-object`), `enum`, `const`, `minProperties`, `maxProperties`; annotations `default`, `description`, `title`, `examples`, `format` anywhere;
  - keyword values have the right shape (counts are whole numbers of 0 or more, bounds are numbers, `multipleOf` > 0, `enum` a nonempty list of distinct values of the type).
  pdd is never stricter than the engine: a rule it cannot judge for sure is not a refusal.
- P9 validator keywords: `type`, `oneOf` (exactly one variant fits), `properties`, `required`, `additionalProperties`, `items`, `enum`, `const`, `minimum`, `maximum`, `exclusiveMinimum`, `exclusiveMaximum`, `multipleOf`, `minLength`, `maxLength`, `minItems`, `maxItems`, `uniqueItems`, `minProperties`, `maxProperties`. A `pattern` miss is only a warning (JavaScript and Python regexes differ). Annotations (`title`, `description`, `default`, `examples`, `format`, `$comment`, `$schema`, `$id`) change nothing. Any other keyword skips that input with a warning. The message is the step, the JSON pointer and the rule in words: `steps[0] input /items/0/quantity is 0. The prompt allows 1 to 20.`
- Warnings never block. Input warnings show for refused tests too. A check value that is a number not in its criterion text (only `equals` and `one_of` checks on `result` or `error`, not on `calls` or `world`, and not `count`): `Warning: the AC1 check expects 899, but the AC1 text says 900.` It fires only for a near miss: the closest number in the text differs from the expected number by at most 10%. A far number (0 saves vs the status 409) measures something else, so pdd stays silent. The count of files sent that are not prompt, story or test files is a calm note, not a warning (see the [runtime client](runtime-client.prompt.md)).

## Story criteria

Port the engine's `explicit_story_criteria` and its 4 regexes exactly: the `## Acceptance` / `## Acceptance Criteria` heading (any case, at a line start, `\n` lines only), one numbered list from 1 with continued lines, and the bullet list in the heading section when there is no numbered list. Use Python `splitlines`, `strip` and `split` whitespace rules. The results must equal the engine for the same text.

## Prose hash

- The interface block is the engine `_INTERFACE` regex (`prompt_program_discovery.py` at 7b03d3ea), in JS with the flags `gi`.
- `prose_sha256` = lowercase hex SHA-256 of the UTF-8 bytes of the text with every block removed. Read the file as UTF-8 and do not change newlines.
- `--fill-hash`, for each Git-visible `*.prompt.md` with a block: `draft` = replace only the string value of `"prose_sha256"` in that block and keep every other byte; no key = refuse that file (`add "prose_sha256": ""`); `approved` and current = no change; `approved` and stale = no change, print the stale text, exit 4. Two blocks or bad JSON refuse that file. `--fill-hash` never sets `approved`.

## Source capture

- Use the Git files. Refuse (exit 4, with the paths) a symlink, a submodule or another non-regular file, and a secret name: `.env*`, `auth.json`, `credentials.json`, `id_rsa`, `id_ed25519`, `id_ecdsa`, `id_dsa`, `.npmrc`, `.netrc`, `.git-credentials`, `.pypirc`, `*.pem`, `*.key`, `*.p12`, `*.pfx`, `*.keystore`, `*.tfstate`, `*.tfvars`, `.docker/config.json`, or a path part `secrets`, `.ssh`, `.codex`, `.terraform`, `.aws`. Refuse more than 10,485,760 bytes or more than 10,000 files, with the total and the 5 largest files.
- Write the tar in memory in Node: ustar, Git names with no `./`, mode 0600, mtime 0, uid and gid 0, empty user and group names, a PAX `path` record for a name that is not ASCII or is longer than 100 bytes, and two zero blocks at the end. The same files give the same bytes. `source_sha256` = SHA-256 of the tar bytes.
- Stat each file before and after (ino, size, mtime in ns). If a file or the file list changes, capture again, at most 3 times; then stop with exit 5.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md). The [runtime client](runtime-client.prompt.md) calls this module.
