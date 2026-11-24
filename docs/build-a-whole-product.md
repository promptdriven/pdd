# Build a whole product

Describe what you want to build — for example, "Build a coffee pickup app: a
phone app to order, a shop server, and a barista screen" — and author the
product map, plan and contracts in your repository. `pdd product` tracks the
plan, topological waves, GitHub issues and PR progress; each planned slice runs
through `/pdd` in your coding agent (or queues cleanly for `pdd autopilot`).

Read the map and answer its questions. Approve the map when it describes what
you want. For coffee pickup, the [example map](../examples/coffee-pickup/product/map.md)
has twelve CORE Stories, three parts and journey J1: order a latte, mark the
ticket done, and see Ready on the phone. Cancellation is LATER.

| Path | Map | Plan |
|---|---|---|
| single part | One cohesive part | Keep the map; run one feature slice. |
| multi-part | Decoupled parts with shared boundaries | Parts, boundaries, contracts and scoped runs. |
| sliced rollout | Broad cross-part rollout | Also vertical slices: slice 1 makes one thin journey work through all parts. |

Choose a path from architecture boundaries rather than fixed Story counts. Keep
each planned run scoped to one cohesive part or contract boundary; runs with
more than 12 Stories receive an advisory warning.

## Files

The files live in your repository so any session can continue. Follow the
[complete coffee example](../examples/coffee-pickup/README.md):

Read the [product guide](../skills/pdd/references/product.md) for the map,
plan tables and contract records. `product/map.md` lists parts, Stories,
journeys, `## Rules to check`, and open questions. `product/plan.md` lists
boundaries, optional `Through:` / `Base:` / `Issue:` preamble settings,
`## Prompts` inventory, and planned `## Runs`. `contracts/` holds shared record
schemas, the world key ownership table and the shared seed.

`plan PR` means `product/plan.md` is present on the integration base branch.
Planned-run needs wait for the implementation PR to merge by default, or for the
prompt PR (or implementation PR) to merge when `product/plan.md` sets
`Through: prompt-pr` or when `--through prompt-pr` is passed. Explicit starts
show unmet needs as advice without blocking you.

Review the plan PR's parts and contracts. The coffee plan has `server-1`,
`phone-1`, `barista-1`, then `journeys`. The phone never talks directly to the
barista screen. Single-part runs test other parts as fakes from their contracts
and do not change `contracts/`. The final `all` / journey run composes every part's maps and prompts in `pdd --product` for prompt-space exploration and proves real unmocked implementation wiring across parts with a cross-part `verify.paths` recipe executed by `pdd prove`.

## Check the plan

Run `pdd product status` to parse the map and plan, audit `## Prompts` inventory
drift and unwired `## Boundaries` operations, and report structural problems
such as duplicate IDs or unknown references. It makes no interpreter calls,
though it reads GitHub for issue and PR status. Run `pdd contracts` (also
available as `pdd product contracts`) to inventory shared records and their
users; unused records can have no users yet.

Review the shared schemas and seed with the map and boundaries. Walk through
normal, refusal and empty-world examples, and confirm that each required domain
boundary and ownership rule is represented. Once prompts and Story tests exist,
run offline `pdd lint` to check prompt structure, rules and contract wiring, and
`pdd test` to verify behavior.

## Start and track runs

After the plan PR is merged and its integration base branch is available locally:

```sh
pdd product next
pdd product start server-1
pdd product start phone-1 --no-run
pdd product status
pdd product status --json
```

`pdd product next` groups planned runs into deterministic topological waves
(`Wave 1`, `Wave 2`, ...). The first three coffee runs share Wave 1 and can run
in parallel or in order. `pdd product start RUN` finds the exact run marker in
an existing trusted issue (including closed issues) before creating one, pins
the integration base commit SHA when available locally, and prints a concise
`/pdd` handoff for your coding agent (or queues with `pdd autopilot start --issue N`).
`--no-run` prepares or reuses the scoped issue without starting a run.

The marker search reads bounded pages, including closed issues. A run belongs to
an issue by a repository owner, member or collaborator, or by the authenticated
GitHub user. An outsider's marker does not claim your run. If trusted duplicates
exist, `pdd product` chooses the issue with a matching local run first, then the
oldest issue, and warns. Long issue titles compact to stay within GitHub's
256-character limit while preserving every Story ID and text in the issue body.

Status counts current passing Stories per part and slice, shows stale results,
waves, PRs and what can start next. A stale pass used older files and needs
another check. On another machine, status reads `Prompt tests` lines in the
run's PR and labels those results `from PR #N`; remote lines are reported
progress rather than locally verified passes. Name each Story file with its map
ID first, for example `P01-menu.md`. `LATER` Stories do not count toward planned
progress. No result files are committed, and these commands make no interpreter
calls.

Only the run's own same-repository PRs count. Status takes check results from
the latest eligible PR with named results, so a code PR without them does not
hide a prompt PR's checks. A run's need is satisfied by a merged same-repository
PR carrying `<!-- pdd-product: run=<RUN> stage=code -->`, a normal merged
same-repository PR that closes the run's issue (`Closes #N` without a prompt-only
stage marker), or a merged PR carrying `<!-- pdd-product: run=<RUN> stage=prompt-pr -->`
when targeting `prompt-pr`. Use `--base BRANCH` (or `Base: BRANCH` in
`product/plan.md`) to target a non-default integration branch. For merged work,
current and stale compare with the base branch's files; if that base is
unavailable locally, status warns and leaves those results unverified. Needs
cycles show their closed path in `status` and `next` as advice without hiding
unrelated ready runs.

Journey J1 is the final run after the three parts. Run cross-part Story checks, explore the composed product in `pdd --product`, and run an unmocked cross-part integration `verify.paths` recipe via `pdd prove` to verify the real implementation path across parts.
Status tracks journeys separately from each part's Stories.
