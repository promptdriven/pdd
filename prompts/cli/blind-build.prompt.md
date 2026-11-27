# Blind build

Own `src/autopilot/blind-build.mjs`. `pdd test --blind-build` asks whether a prompt alone is enough to build its module. Fresh agents get only the prompt and its declared dependencies, never the approved cases, the existing code or any chat. pdd then runs the Story cases on what they built, and with two builds it compares the builds on the same inputs. The result shows where the prompt allows more than one reading, so a person can decide and write it down.

## Domain decisions

- **Why blind.** A passing `pdd test --target code` shows that the code matches the cases. It does not show that the prompt says enough: an agent that saw the cases, the code or the chat can match them without the prompt. When one agent reads a rule once and writes both the cases and the code, a misreading passes on both sides (#3272). A builder that never saw the cases removes that shared point of failure.
- **Opt-in only.** Blind build calls agents and costs money. It runs only on `pdd test --blind-build`; no other command or Autopilot run starts it.
- **What a builder gets.** The selected Stories' entry prompts and their declared dependencies, exactly the prompt files that `captureSource` selects for those Stories, minus every Story file (`user_stories/`), every scenario file (`tests/`) and every selected scenario path. Each prompt keeps its Runtime interface block: the schemas and `implementation.command` are part of the contract. No code file, Git data, report or chat goes in. The packet keeps each file's repository-relative path so links between prompts still resolve.
- **Isolation by folder and instruction.** Each agent works in its own new folder outside the repository, under the system temporary directory, holding only the packet. Its brief says to read only that folder. This is not a sandbox: the agent runs with full access, like Autopilot's agents, and could read other paths. The report says so (`isolation: "folder"`).
- **Three roles.**
  - **Builder** (1 or 2, each fresh): writes the implementation so each entry's `implementation.command` runs from its folder, and writes `pdd-decisions.json` listing every choice it made that the prompt did not decide.
  - **Prober** (only with 2 builds, fresh, prompt packet only): writes `pdd-probes.json`, the places where it thinks the prompt allows more than one reading, each with inputs that would tell the readings apart. It never writes expected values: deciding them is the person's job, and an agent's guess would bring the shared point of failure back.
  - **pdd** (no AI): runs the Story cases on each build, runs every collected input on both builds, compares, and merges the three sources.
- **Builder decisions are leads, not proof.** A builder misses choices it did not notice (for example accepting `-0`). Differences between two builds are measured; decisions and probes are agent text. The report keeps them apart.
- **Comparing builds.** Compare the full result of every input (`exit_code`, `stdout` and `stderr`, exactly), not only the fields a case checks, except that each build's own folder path (as given and as resolved) in `stdout` or `stderr` becomes `BUILD`: the folders differ by name, so an error message that names a file would otherwise always differ. Only two finished builds are compared; when either build did not finish, there is no comparison and the report says why. Inputs come from three sources: every runnable case step, every decision example and every probe input. An input that the entry's input schema does not admit is dropped and listed with the reason; it is never run.
- **Outcome.** Exit 0 only when every case step of every build passed and, with 2 builds, every compared input agreed. Any failed or not-run case, any difference, any builder that failed to finish, or any unknown commit exits 1. Selection errors and invalid options exit 2. A not-run step never counts as passed.

Each reported item lands in the first group whose condition holds, checked in this order:

| Order | Condition | Group |
|---|---|---|
| 1 | its inputs gave different results on the two builds | Builds disagree |
| 2 | a probe with 0 separating inputs | Reported, no input separates the readings |
| 3 | its inputs were compared and agreed | Reported, builds agree |
| 4 | otherwise (one build, a build did not finish, or no input to run) | Reported, not compared |

## Public contract

`runBlindBuild({root, words, builds, agent, timeout, resume, json}, ports)` is async and returns the exit code.

- `root` is the invocation working directory; `words` selects Stories as in `pdd test --target code`; `builds` is 1 (default) or 2; `agent` is an optional agent name or id; `timeout` is minutes per agent run (default 30); `resume` is a run ID to continue (see Checkpoints); `json` selects JSON output.
- `ports`: `stdout`, `stderr`, `spawn` (synchronous process runner, default `spawnSync`), `runAgent({agent, cwd, input, env, log})` (async; resolves `{code}`), `agents` (agent definitions, default `loadAgentDefinitions`), `tmpdir` (default `os.tmpdir()`), `env` (default `process.env`), `now` and `id`.
- Agent choice: `agent` matches a definition's `name` or `id`, ignoring case; without it, the first definition. An unknown name prints `Unknown agent: NAME` to `stderr` and exits 2 before any work. The agent command and arguments come from `agentCommand`. The agent's environment is `jobEnvironment(env, {stripGithubTokens: true})` plus the definition's own `env`, so a builder cannot change GitHub. Builders and the prober run at the same time. An agent run that passes its time limit is stopped (the whole process group) and counts as not finished.
- Steps:
  1. Resolve the Git root and the selected Stories with the compiled checker's selection rules. Only Stories with at least one runnable CLI step can be built; when none has one, print `Blind build needs a Story with a CLI entry: STORY: REASON` lines and exit 2.
  2. Build the packet and write the manifest to `.pdd/blind-build/ID/manifest.json`: `{id, commit, dirty, stories, files: [{path, sha256, bytes}], excluded: ["user_stories/", "tests/", "selected scenarios", "code", "chat"], isolation: "folder"}`.
  3. Make `TMP/pdd-blind-ID/build-N/` (and `probe/` with 2 builds), copy the packet into each, and start the agents with the briefs below. Agent logs go to `.pdd/blind-build/ID/build-N.log` and `probe.log`.
  4. For each finished build, run the compiled checker with `implementationRoot` set to the build folder. An unfinished build is not checked.
  5. With 2 finished builds, run each collected input on both builds with the compiled checker's CLI rules and compare.
  6. Write the report to `.pdd/blind-build/ID/report.json` and `.pdd/blind-build/latest.json`, then print it.
- Same `.pdd` symlink guards and `.pdd/.gitignore` seeding as the compiled checker. The build folders are kept so a person can read the code; the report names them.

### Briefs

Every brief lists each entry prompt with its `implementation.command` and its input schema, and says that every input it writes must match that schema exactly, using only the fields the schema lists, because an input the schema does not admit is dropped. (In a first real run, agents shown a sample input with `stdin` added it to every input of an entry whose schema has no `stdin`, and every decision and probe was dropped.)

The builder brief names the folder and says:

- Build the module from these prompts only. Read only files in this folder. Do not look for tests, other code or Git history anywhere else.
- Make each command run from this folder.
- Write `pdd-decisions.json`: a JSON array of `{topic, prompt_says, choice, example}` where `prompt_says` quotes the prompt words that left the choice open or is `"silent"`, and `example` is one entry input (`{entry_path, operation, input}`) where the choice shows. List every choice the prompt did not decide, including small ones (number formats, signs, leading zeros, rounding, order of errors).

The prober brief names the folder and says: do not write code; read only this folder; go through the prompt sentence by sentence with the questions below; write `pdd-probes.json`, a JSON array of `{topic, readings, inputs}` where `readings` lists the readings in words and `inputs` lists entry inputs `{entry_path, operation, input, outcomes}`, with `outcomes` saying in words what each reading gives for that input, one per reading in order. It must choose inputs whose outcomes differ between readings, and never say which reading is right.

The questions are general, so that the prober finds whole kinds of second readings in any domain rather than only those its instinct suggests. Blind build exists to catch these, and a prober left to itself missed one: in a real run on a tip calculator it asked how the per-person amount is rounded but never asked which total is divided, and its inputs had whole cents, where both readings print the same.

1. Which value is meant: when a name comes back later, is it the value before or after an earlier step changed it (rounding, trimming, sorting, normalizing, filtering)?
2. Same value, different form: are inputs that mean the same thing but are written differently treated alike (case, extra spaces, `2` and `2.0`, relative and absolute paths, an empty string and a missing value)?
3. Edges: exactly at a limit, just past it, empty, one item, very large.
4. Rules that overlap: when two rules apply to one input, which wins (for example, which error comes first)?
5. What the prompt never mentions: one argument too many or too few, repeated items, unusual characters.
6. Parts that must agree: do the parts of one output agree with each other (parts that add up to a printed whole, a count that matches a list), and could a reading make them disagree?
7. Order and format: the order of output lines or items, spaces, the final newline, letter case.

pdd does not generate inputs of its own: knowing which inputs are tricky needs the domain, and that knowledge belongs to the agents that read the prompt. A probe input separates its readings when its `outcomes` has one entry per reading and not all are equal; the report counts them per probe as `separating_inputs`.

A missing or malformed decisions or probes file is reported (`decisions: null`, with the reason) and never stops the cases.

### Checkpoints

An agent that runs out of time may only need more time, or it may be stuck on a bug in the prompt, its code or the tools. A person cannot tell which from a timeout alone, so every brief also says: keep `pdd-progress.json` up to date after each step, as `{status, done, doing, stuck_on}`, where `status` is `working`, `done` or `stuck`, `done` lists finished steps in words, `doing` is the current step and `stuck_on` names what blocks it (an error message, a failing command, a prompt sentence it cannot read one way) or is null.

- The agent time limit is `--timeout MIN` (1 to 120, default 30) per agent run.
- When an agent run ends without finishing (time limit, nonzero exit, or no command file), the report keeps its last `pdd-progress.json` (or `null` with the reason) and the last 20 lines of its log as `checkpoint: {progress, log_tail, reason}` on that build or the probe. Text output prints `build-N not finished (REASON): doing DOING; stuck on STUCK_ON`, then, when there is no progress file, `last log line: LINE` (often the only clue, for example an agent that refused its model or is not logged in), and the folder.
- `pdd test --blind-build --resume ID [--timeout MIN]` continues run `ID`: it starts a new agent in each unfinished build or probe folder, with the same brief plus the saved checkpoint and the words `continue from this checkpoint`. Finished builds are kept. The folders still hold only the packet and the agent's own work, so the build stays blind. Then it runs steps 4 to 6 again for the whole run and writes a new report. An unknown ID, a run whose folders are gone, or a changed packet (any manifest sha256 differs from the current prompts) prints the reason and exits 2.

### Report

`{target: "blind-build", id, commit, dirty, agent_runs, agent, isolation: "folder", manifest, builds, comparison, decisions, probes}`:

- `builds`: one per build, `{build, folder, finished, checkpoint, cases: {passed, total}, stories}` (`checkpoint` is null for a finished build), where `stories` has the compiled checker's Story rows. An unfinished build has `cases: null` and `stories: []`.
- `comparison` (null with 1 build, and null with `comparison_skipped: "build-N not finished"` when a build did not finish): `{inputs, agreed, differences, dropped}`. Each difference is `{source, topic, entry_path, operation, input, results}` with `source` `case`, `decision` or `probe`, and `results` one `{exit_code, stdout, stderr}` (or `{not_run: REASON}`) per build. `dropped` lists `{source, topic, input, reason}`.
- `decisions`: per build, the list from `pdd-decisions.json` with `differs` set to true, false or null (not compared) for its example.
- `probes`: the prober's list with `differs` per probe (true when any of its inputs differs) and `separating_inputs`.

Text output prints one summary line, then the details:

```
Blind build: 12/12 cases · 2 builds agree on 40/42 inputs · 5 decisions, 3 probes
```

With one build: `Blind build: 12/12 cases · 1 build · 5 decisions`. With 2 builds the cases part is `12/12, 11/12`; an unfinished build shows `not finished` there, and the comparison part becomes `builds not compared`. Then each difference (input and each build's result, `decision`/`probe` topic when known), then decisions and probes grouped as: `Builds disagree` (a difference was measured), `Reported, builds agree`, `Reported, no input separates the readings` (a probe with no separating input: agreement on such inputs says nothing, so a person must decide), `Reported, not compared`. Then `Dropped N inputs, never run: REASON (COUNT); …` when any input was dropped, then any not-run steps and the manifest and report paths. Long values in text output are cut at 300 characters; the JSON report keeps them whole. JSON output prints the full report.

## Dependencies

- [Compiled Story checker](compiled-test.prompt.md): Story selection, CLI step rules, `implementationRoot` and the CLI input runner.
- [Runtime seam](runtime-seam.prompt.md#public-contract): `captureSource` selects the prompt packet; `checkInput` admits inputs.
- [Headless agent jobs](agent-job.prompt.md#public-contract): `agentCommand` and `jobEnvironment`.
- [Agent definitions](agent-config.prompt.md): `loadAgentDefinitions`.
