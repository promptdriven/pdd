# Story guide

A Story says what one person can do and what they see then.
Its test checks each numbered criterion against the prompt.
The person reads and approves the Story in about one minute.
Read this page in full before you write or change a Story.
RUNBOOK §2 owns the file formats. This page restates them in short.

## The files

- The Story is `user_stories/<story>.md`. `user_stories/PLAN.md` is an index, not a Story.
- Its test is `<story>.json` in a folder named `tests` or `test` (RUNBOOK §2 names the folder when the repo already has tests/).
- The test copies each criterion into `criteria`, word for word.
  A criterion that wraps over lines is one line in the test, with one space at each line break.
- One behavior is one Story. For more behaviors, write more Stories and list them in `user_stories/PLAN.md`.

## The parts of a Story

1. `# Title`: the action, in a few words.
2. One line: "As a <role>, I want <action>, so that <reason>."
   The PR shows this line as the user story. pdd finds it only with "As a" (or "As an"), "I want" and "so that".
3. `## Acceptance criteria`: a numbered list from 1. A test checks only these lines.
4. Only when you need them: `## What must not change` and `## Rules to check`. Use bullets (`-`) there.
   Number only the criteria. pdd can read a numbered list in another part as criteria.

A good Story (the criteria of the `todo-cli` example in RUNBOOK §2):

```markdown
# Finish a task

As a person who keeps a to-do list in the terminal, I want to mark a task as done, so that I see what is left.

## Acceptance criteria

1. `todo done 4` prints "Done #4: Call mom", exits with code 0 and saves task #4 as done.
2. Task #1 stays not done.
3. `todo done 9` prints "todo: no task #9" to stderr, exits with code 1 and saves nothing.
```

## Five rules

1. **Name the person.** Use a role: "a customer", "a shop owner", "a developer who runs `pdd test`".
   Do not write "the user" or "the system". Use the words of the issue.
   Use real names and values: "Sam", "08:30", "$9.00".
2. **One criterion = one action and its result.** Say what the person does, and what they see or what is saved.
   If "and" joins two actions, split them. Name no functions or types. A command that the person types is fine.
   Do not write "correctly", "gracefully" or "as expected". A test cannot see them.
3. **Every criterion needs an exact check.** It needs at least one `equals`, `not_equals`, `one_of`, `count`,
   `at_least`, `at_most`, `not_contains`, `all_in` or `equals_ignore_case` check on one of the four places below
   (or HTML `exists`; RUNBOOK §2, §8, §20). A criterion with no exact check is "not checked".
   The other criteria still run, but the Story is not a full pass. In a normal run, pdd then does not open PR 1
   by itself. A test with no exact check at all is refused (`unchecked-criteria`), and pdd sends nothing.
4. **"Does not" and "stays the same" need something to watch.**
   - "Saves nothing" or "calls X 0 times": OK when the prompt declares that operation. The test counts it on `calls`.
   - "X stays the same": OK when X is in the test's saved data. The test reads it on `world` after the step.
   - "When Y fails, …": OK when Y is a declared resource. The test supplies its reply, so it can supply
     a failure reply that the result schema allows (RUNBOOK §21). Real disk failures (permissions, a full disk,
     fsync, rename) need native tests.
   - Anything else is not a criterion. Read "When a test cannot see it" below.
5. **Keep it small.** One behavior per Story, usually 1 to 4 criteria. Long data goes in the test, and the Story
   says it in plain words. Build notes, PR links and run results go in the PR, not in the Story.

## What a test can see

| Place | What it sees | In the good Story |
|---|---|---|
| `result` | The answer: printed text, exit code, returned fields | 1 and 3: the printed text and exit code |
| `error` | The error code of a step that the prompt refuses | (Harbor Coffee in RUNBOOK §2: `unknown-item`) |
| `world` | The saved data after the step | 1: task #4 is done. 2: task #1 is not |
| `calls` | How many times a declared resource operation or a called prompt ran in the step | 3: the save count is 0 |

Do not check words that the AI picks freely, or generated IDs.
Quote text only when the person must see exactly that text.

## When a test cannot see it

A test cannot see an effect that the prompt does not declare.
It also cannot see the real disk, Git or processes, signals, two commands at the same time,
keyed hashes (HMAC), signatures or typing in a browser.
A test checks a page through what its `render` operation returns. A SHA-256 needs a `compute` resource (RUNBOOK §21).

- **A precise rule** goes under `## Rules to check`: money and rounding, limits, who may do what,
  the order of states, parsers, or an effect that must never happen.
  Write one bullet for each rule, with its forbidden result. `pdd test` does not read this part.
  In the code PR, an agent that did not write the code proves each rule against the real code
  (the formal check, RUNBOOK §17). The code PR is not ready to merge until that result is recorded.
- **Other behavior** goes to the native tests of the code PR (the repo's own tests). `pdd test` does not run them.
  Say in the PR that `pdd test` does not check this behavior.
- **`## What must not change`** tells the person what stays the same. The Story card shows it, but no test reads it.
  If a test must check it, write it as a criterion: "Task #1 stays not done."

## Bad to good

```markdown
As a user, I want renaming to be robust.
1. Renaming a task works correctly and errors are handled gracefully.
2. Renaming starts no sync.
3. If the save fails, the task list stays unchanged.
```

Who is "a user"? What do "robust" and "correctly" look like? The line has no "so that", so the PR shows no user story.
There is no `## Acceptance criteria` heading, so pdd does not find a Story in this file.
The prompt declares no sync call, so the test has nothing to count: criterion 2 is not checked.
In the todo test, the save writes saved data and always works, so nothing makes criterion 3 happen. The rewrite:

```markdown
# Rename a task

As a person who keeps a to-do list in the terminal, I want to rename a task, so that I can fix a typo.

## Acceptance criteria

1. `todo rename 4 Call dad` prints "Renamed #4: Call dad", exits with code 0 and saves task #4 as "Call dad".
2. `todo rename 9 Call dad` prints "todo: no task #9" to stderr, exits with code 1 and saves nothing.

## Rules to check

- A rename changes only the text of the named task. Forbidden: another task changes, or a done state changes.
- If the save fails, the saved list keeps its old content. Forbidden: a list that is saved in part.
```

If the sync matters, declare it in the prompt as a resource.
Then criterion 1 can end with "and starts no sync", and the test counts the sync calls (0).

## Before you show it

- Read it as the person. Can they approve it in one minute?
- For each criterion, name its place: `result`, `error`, `world` or `calls`.
- Check the "As a …, I want …, so that …" line.
- Use straight quotes ("), not curly quotes. Text from an issue often has curly quotes.
  Then the test text does not match the Story (`story-criterion-mismatch`).
- `pdd lint STORY` uses 0 AI calls and prints each criterion that is not checked.
  Do not run it right before `pdd test`: `pdd test` includes lint (RUNBOOK §11).
