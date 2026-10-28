# Prompt approve

Own `src/prompt-approve.mjs`. Export `runApprove({words, cwd}, ports)` (returns an exit code) and `approvePromptText(text)` (returns the approved text or null). `pdd approve PROMPT` is the one way pdd sets `"status": "approved"` (Serhan, Oct 27, #9). It is for people only: it needs a real terminal and the person's own `y`.

## Steps

1. PROMPT is one path (relative to cwd). It must be a Git-visible `*.prompt.md` file in the repo (`git rev-parse --show-toplevel`), else exit 2: `<path> is not a Git-visible *.prompt.md file in this repository.`
2. No real terminal (stdin and stdout are not both a TTY): exit 2, `pdd approve is for a person at a terminal. Ask the person to run: pdd approve <path>`. Nothing changes.
3. The file needs exactly one Runtime interface block with valid JSON, else exit 4 with the reason.
4. Approved and the hash is current: print `<path> is already approved and current.` and exit 0.
5. The interface must pass the engine schema rules ([runtime preflight](runtime-preflight.prompt.md) `interfaceSchemaProblems`). Else print each problem (code, JSON pointer, rule), `Fix these before you approve.`, exit 4.
6. Show the interface in plain words: `<path> (<status>)`, then for each entry `Operation <name>`, `Input:` and `Result:` with one line for each field (`name: type, rule`; nested lists and objects indented; a field not in `required` is `(optional)`; an enum is its values; `oneOf` is its variants joined with `or`), and `Errors: …`. Then the calls and resources when there are any. Then the text that the person approves (round-2 tester: the screen showed only the interface, and the change was in the prose). The prose is the file text without the interface block. The last approved version is the newest Git commit (of the last 200 that touch the file) whose version of the file has `"status": "approved"` with a `prose_sha256` that equals its own prose hash. With one: `Text changes since the last approved version (<first 12 of its commit>):` and the changed lines, `  - ` for a removed line and `  + ` for an added one, with 1 unchanged line around each change (`    ` in front) and `  …` between parts; or `Text: the same as the last approved version (<commit>).` With none: `Text (no approved version in Git, so all of it):` and every prose line, 2 spaces in, without the empty lines at the end. Show at most 40 of these lines, then `… N more lines not shown.` and `See all of them with: git diff <commit> -- <path>` (or `Read the whole file: <path>`). Never cut inside a line; remove control characters so that terminal codes cannot hide text. When the prompt was approved but its text changed: `The text changed after it was approved. Read the prompt again before you answer.`
7. Ask `Approve <path>? y/n ` and read one line. Only `y` or `yes` (any case) approves. Anything else, or no answer: `Not approved. Nothing changed.`, exit 1.
8. On yes: set the top-level `"status"` to `"approved"` and the top-level `"prose_sha256"` to the current prose hash, and keep every other byte (a nested `status` field is never touched). Check that the new text parses to the same interface with only those two values changed and that its prose hash is unchanged. Print `Approved <path>.`, exit 0. If the block has no `prose_sha256` key, exit 4: `Add "prose_sha256": "" to the Runtime interface, then run pdd approve again.`

Ports (tests inject them): `stdout`, `stderr`, `stdin`, `interactive` (default: stdin and stdout are TTYs).

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md). The [CLI](pdd-cli.prompt.md) routes `pdd approve PROMPT` here. The [runtime client](runtime-client.prompt.md) uses the same view and edit for Try-page approvals.
