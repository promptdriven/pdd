# Open my program the way I use it

I can run `pdd simulate` and use my program in a shell, with localhost requests,
or on the Simulator page, without choosing flags first.

## Acceptance criteria

1. In a project with command-line, HTTP and screen Stories, `pdd simulate cli` opens a shell with the command ready; `pdd simulate http` starts localhost and prints its URL and one curl example; `pdd simulate screen` opens the Simulator page.
2. `pdd simulate` with no Story opens the whole app with every mapped screen, or the unique main command-line program; without either, it serves the project's HTTP routes.
3. `pdd simulate screen --cli` explains that this Story is not a command-line program and lists the command-line Stories, without asking me to understand schema or RUNBOOK terms.
4. `--cli`, `--cli --shell` and `--serve` keep working; `--shell` opens the command-line shell, and `--page` lets me choose the Simulator page even for a command-line Story.
5. Help, feature and bug skill advice, and the Story gate explain the same automatic choice and say I can omit the Story to open the whole project.
6. If the project has several different command-line programs, `pdd simulate` asks me to name a Story and lists the choices instead of starting an arbitrary program.

7. A Story whose operation takes typed commands and returns a structured answer opens on the Form tab with one plain explanation, including when another Story has the project's screen map; a Story actually mapped to a screen still opens Screen.
8. For that typed Story, `--cli` or `--shell` exits 125, explains it is not a command-line program, lists eligible command-line Stories and says `pdd simulate typed` opens its Form tab. No message asks me to add conventions or an adapter, including when the CLI adapter is called directly.
9. Help lists `pdd simulate [STORY] --page [--new]` as its own form.

## Rules to check

A named Story chooses command-line first, HTTP second, then the page. Explicit
page requests, including the existing agent and tab options, retain their page
behavior. Whole-project screen selection uses every mapped screen. Several
Stories for the same command-line entry describe one main program; several
entries do not establish a main program. Refusals for a locally known mismatch
happen before sign-in or remote requests. Existing saved sessions and their
budgets remain intact when the way of opening changes.

Native cases: [simulation selection](../test/simulate-kind.test.mjs) and the
`2760` Story-gate case in [workflow runner](../test/workflow-runner.test.mjs).
These use synthetic repositories and fake transport with injected shell,
browser and server-observation ports. They make no model or interpreter calls.
Runtime check: NOT RUN; this task authorizes Node regressions only. Actual
interactive shell, browser display and live interpreter behavior remain unproved.
