# File owner lookup

Own `src/file-owner.mjs`. It answers one question for a repository file: which
prompt owns it. Autopilot, code replay and the check plan need the same answer,
so this module owns the one `Generated from` header reader and the one owner
lookup. It reads local files only. It changes no file, signs in to nothing and
calls no interpreter.

## Owner records

Three records can name the owner of a path. Read them in this order:

| Source | Record | Certain |
|---|---|---|
| `binding` | An entry of the root `pdd-bindings.json` (`pdd.bindings.v1`) whose `module` is the path. Its `prompt` names the owner. | yes |
| `header` | A [`Generated from` header](#generated-from-header) in the first 4 KiB of the file. | yes |
| `prose` | A [prompt claim](#prompt-claims): the first sentence of a prompt's opening paragraph names the path. | no |

`owners` is the list of prompts that the binding and the header name, binding
first, then headers in line order, without duplicates. Only when that list is
empty, `owners` is the sorted list of prompts that claim the path in prose.
`owner` is the first entry of `owners`, or null. `source` is the source of
`owner`; with no owner it is `binding` for a binding entry without a prompt,
otherwise null.

`certain` is false when the answer can be wrong in the unowned direction.
Callers treat a path with `certain: false` as owned. It is false when:

- the owners come from prose only;
- a binding or header names a prompt that is not a Git-visible `*.prompt.md`
  file;
- no owner is found and `pdd-bindings.json` exists but is not valid JSON, is
  not an object with `schema_version` `pdd.bindings.v1` and a `modules` array,
  or cannot be read;
- no binding names a prompt and the file exists but cannot be read.

Otherwise `certain` is true. A binding entry without `prompt` (it has `reason`
and `port_attempt` instead) names no owner; prose claims still apply, and without
a header or a claim it is certain that no prompt owns the path. Binding entries that are not objects with a string `module` are
skipped; a string `prompt` names the owner.

`note` explains an uncertain or prompt-less answer in one line, else it is `''`.
Join several notes with `; `, in this order:

- prose only: `named only in the opening sentence of PROMPT; add a Generated from header or a pdd-bindings.json entry`
  (PROMPT lists the owners, joined with `, `);
- a missing prompt: `names PROMPT, which is not a Git-visible prompt` (one note per missing prompt);
- unreadable bindings: `pdd-bindings.json could not be read, so a binding may be missing`;
- unreadable file: `the file could not be read, so a header may be missing`;
- binding without a prompt: `pdd-bindings.json declares it with no prompt`.

### Generated from header

A header line names the prompt that a file was generated from. Read only the
complete lines inside the first 4,096 bytes of the file (decode as UTF-8; when
the file is longer, drop the last line of that window because it can be cut).
Skip lines longer than 1,100 characters. A header line is, in order: optional
white space, an optional comment opener (`//`, `#`, `--`, `;`, `/*`, `*`,
`<!--`, `"""` or `'''`, each of the repeatable marks repeated), optional white
space, `Generated from `, PATH, optionally ` (sha256: HEX)` with 64 lowercase
hex digits, optionally `.`, optional white space, an optional closer (`*/`,
`-->`, `"""` or `'''`) and optional white space. PATH has no white space and
ends in `.prompt.md`. Other text, such as `Generated from the canonical m1_policy
prompt` or a `Generated from` inside a string, is no header. A file can have
more than one header; each names an owner. The header can be on any line in the
window, for example after a `#!` line, a license or imports. HEX is the
[header hash](#header-hash) of the prompt that the file follows.

A canonical path is a nonblank string of at most 1,000 characters, not absolute,
with no backslash, no control character and no empty, `.`, `..` or `.git`
(any case) segment. Drop header paths that are not canonical.

### Header hash

The header hash of a prompt is the SHA-256 (64 lowercase hex digits) of the
UTF-8 bytes of its behavior text. The behavior text is the prompt text with
the approval metadata taken out: replace the JSON of each Runtime interface
block (found with the shared [interface block reader](runtime-preflight.prompt.md))
that parses as a JSON object with `JSON.stringify` of that object without its
top-level `status` and `prose_sha256` keys. Keep all other bytes. A block whose
JSON does not parse as an object stays as written.

So the hash covers the prose and every interface declaration: entries,
operations, schemas, errors, calls, resources, limits, kind, reason and
conventions. It ignores the approval metadata: `pdd approve` and
`pdd test --fill-hash` change only `status` and `prose_sha256`, and approval
evidence is kept outside the prompt. Approving a prompt therefore leaves its
headers current. It also ignores white space inside the interface JSON.

Each header has a hash state:

| State | When |
|---|---|
| `current` | HEX equals the header hash of the named prompt. |
| `current` with `legacy: true` | HEX equals the SHA-256 of the whole prompt file (the earlier form, which every approval changed). pdd accepts this form as current for compatibility and marks it `legacy: true`; write the expected hash for a canonical header. |
| `stale` | HEX is any other value: the prompt changed after the header was written. |
| `none` | The header has no hash. |
| `unknown` | The named prompt is not a Git-visible prompt, or its content is not available. |

A stale or missing hash is a report, not an error. Writing the hash is the
writer's claim that the file follows that prompt version; pdd computes the hash
and never rewrites a header.

### Prompt claims

The opening paragraph of a prompt is its first block of text. Skip leading
blank lines and one `# ` title line, then blank lines. The paragraph is the run
of lines up to a blank line, a heading line (`#`) or a code fence (```` ``` ````
or `~~~`). A prompt that starts with a heading or fence after its title has no
opening paragraph. Join the lines with single spaces.

The claim sentence is the paragraph up to and including the first `.`, `!` or `?`
that is outside a backtick span and is followed by white space or the end of the
paragraph; without one, the whole paragraph. Only this first sentence claims
paths: later sentences often name files that the module reads, such as `pdd.json`.

The claimed paths are:

- each Markdown link target `[text](TARGET)` in the sentence, without its
  `#fragment`, resolved against the prompt's folder; skip a target with an empty
  file part or a URL scheme (such as `https:`);
- each other run of the characters `A-Z a-z 0-9 _ @ + ~ . / -` that contains a `/`
  or a `.`, without trailing `.` characters. A run that starts with `./` or
  `../` resolves against the prompt's folder; any other run is
  repository-relative.

Keep only canonical paths. Drop paths that end in `.prompt.md`: a prompt names
other prompts as links, not as owned files. A claim does not need the file to
exist: a prompt is written before its code.

## Public contract

- `headerPrompts(content)`: content is a string, a `Uint8Array` (including a
  Buffer), `null` or `undefined`. A string is read as its UTF-8 bytes. Return
  the canonical header paths in line order, without duplicates; `[]` for no
  content.
- `headerEntries(content)`: like `headerPrompts`, but return `{prompt, sha256}`
  rows, with `sha256` the header's HEX or null. When a prompt is named twice,
  keep its first row.
- `promptHeaderHash(content)`: the [header hash](#header-hash) of one prompt's
  content (a string or `Uint8Array`).
- `headerHashState(sha256, promptContent)`: return `{expected, state, legacy}`
  for one header. `expected` is the header hash, or null when `promptContent`
  is null or `false` (then `state` is `unknown`). `legacy` is true only for the
  whole-file form.
- `promptClaims(promptPath, content)`: return the sorted, unique claimed paths
  of one prompt; `[]` for no content.
- `isTestOwnedPath(path)`: return `true` when `path` is a canonical
  non-`.prompt.md` repository path inside `test/`, `tests/` or `__tests__/` at
  any depth, or whose file name matches `*.test.*`, `*.spec.*`, `test_*.*` or
  `*_test.*`.
- `resolveOwners({paths, bindings, heads, prompts})`: pure. `paths` is the list
  of canonical repository paths to answer, in order; a repeated path is answered
  once, at its first place. `bindings` is the text of `pdd-bindings.json`, or
  null when it is absent; `false` when it exists but cannot be read. `heads` is
  a list of `{path, content}` rows: content is the file's first 4,097 bytes (the
  whole file when it is shorter) as a string or `Uint8Array`, null when the file
  is absent, or `false` when it exists but cannot be read. The extra byte shows
  whether the last line of the 4 KiB window is cut. A path without a row has no header. `prompts` is a
  list of `{path, content}` rows for every Git-visible `*.prompt.md` file, with
  the whole file as content, or `false` when it cannot be read whole. Claims read
  the first 65,536 bytes of it.
  Return `{schema_version: 'pdd.owner.v1', files}`, where each row is
  `{path, owner, owners, source, certain, note, headers}` as above, in `paths`
  order. `headers` lists one `{prompt, sha256, expected, state, legacy}` row for
  each `headerEntries` row of the file, in line order; `[]` without a header.
- `findOwners({root, paths}, ports = {})`: read the inputs of `resolveOwners`
  from the working tree of the Git root `root`, then return its result.
  `ports.files()` returns the Git-visible repository paths (default: the shared
  [Git file list](runtime-preflight.prompt.md)). `ports.read(path, limit)`
  returns at most `limit` bytes of the working file as a `Uint8Array`, or null
  when it does not exist (default: read the regular file at `root/path`; a
  missing file or a missing parent folder is null; other errors throw, and the
  caller records `false`). Read 4,097 bytes of each requested path (one byte
  more than the header window, so that a cut last line is dropped), 65,536
  bytes of `pdd-bindings.json` (a longer bindings file does not parse, so it
  counts as unreadable) and up to 10 MiB of each prompt (read 10 MiB and one
  byte; a longer prompt counts as `false`).
- `runOwner({cwd, paths, json}, {stdout, stderr, files, read})`: the
  `pdd owner PATH... [--json]` command. Return the exit code.

## The owner command

Find the Git root of `cwd` with `git rev-parse --show-toplevel`. Outside a Git
repository, write `pdd owner works inside a Git repository.` to stderr and
return 2. Resolve each PATH against the real path of `cwd`, then make it
relative to the Git root with `/` separators. When a PATH is not a canonical
path inside the repository, write `PATH is not a file path inside this
repository.` to stderr (PATH as typed) and return 2 before any output.

With `--json`, print the `resolveOwners` result as JSON and a newline. Without
it, print one line for each path:

- `PATH: OWNERS (SOURCE)` with the owners joined with `, `;
- with `certain: false`, add `, not certain: treat as owned` inside the brackets;
- with no owner: `PATH: no owner`, or `PATH: no owner (not certain: treat as owned)`;
- when the note is not empty, print it on the next line after two spaces;
- for each header that is not plain `current`, print one more line after two
  spaces: `PROMPT header hash is stale (HEX); current is EXPECTED`,
  `PROMPT header has no hash; current is EXPECTED` or
  `PROMPT header uses the whole-file hash; current is EXPECTED`. An `unknown`
  state adds no line.

Return 0. The answer is an inventory, not a check: an uncertain or missing owner
is no error. Before returning 0 (in both text and `--json` modes, leaving stdout
unchanged), emit a non-blocking warning to stderr whenever a prompt claims
ownership of a test file (`isTestOwnedPath`):

- for each resolved row in `result.files` with `owners.length > 0` and
  `isTestOwnedPath(row.path)`: write `Warning: misplaced prompt owner: PATH is claimed by OWNERS (SOURCE). Prompts own production modules, not test files.`
- for each explicitly requested `*.prompt.md` path in `paths`, resolve Git-visible
  `isTestOwnedPath` files plus any canonical claimed test paths from
  `pdd-bindings.json` and `promptClaims`, reading file headers only for
  Git-visible regular files (`visible`) and keeping non-Git-visible or symlinked
  claimed paths name-only (`content: null`) so untracked, symlinked or
  out-of-repo paths are never opened from disk; when that prompt claims test
  targets not already warned above, write `Warning: misplaced prompt owner: PROMPT claims TARGETS. Prompts own production modules, not test files.`

## Callers

[Code replay](workflow-replay.prompt.md) and the [check plan](runtime-check-plan.prompt.md)
read headers with `headerPrompts`. They use bindings and headers only; prose
claims never select replay scenarios or check targets. They read the prompt
path of a header, not its hash.

## Dependencies

- [Runtime preflight](runtime-preflight.prompt.md): required generation context
  for `gitFiles(root)`, the Git-visible file list, and `interfaceBlocks(text)`,
  the Runtime interface block reader.
