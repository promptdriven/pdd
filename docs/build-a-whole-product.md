# Build a whole product

Say: "Build a coffee pickup app: a phone app to order, a shop server, and a
barista screen." Call `$pdd-product` in Codex or `/pdd-product` in Claude Code.
The skill makes a product issue and starts `pdd workflow run product ISSUE`.
It makes and tracks the plan. Normal feature runs build each part.

Read the map and answer its questions. Approve the map when it describes what
you want. For coffee pickup, the [example map](../examples/coffee-pickup/product/map.md)
has twelve CORE Stories, three parts and journey J1: order a latte, mark the
ticket done, and see Ready on the phone. Cancellation is LATER.

| Path | Map | Plan |
|---|---|---|
| small | About 10 CORE Stories, 1 part | Keep the map; run one feature run. |
| medium | 10–50 Stories, 2–5 parts | Parts, boundaries, contracts and small runs. |
| large | More than 50 Stories or more than 5 parts | Also slices: slice 1 makes one thin journey work through all parts. |

The agent recommends a path; you can change it at the map gate. A planned run
should fit about twelve Stories or five new prompts. Larger runs get a warning.

## Files

The files live in your repo so another session can continue. Follow the
[complete coffee example](../examples/coffee-pickup/README.md):

Read the [file formats](../skills/pdd-product/references/files.md) for the map,
plan tables and contract records. `product/map.md` lists parts, Stories, journeys
and questions. `product/plan.md` lists boundaries and runs. `contracts/` holds
shared record schemas, the world key ownership table and the shared seed.

`plan PR` means `product/plan.md` is present on the base branch. Planned-run
needs wait for the implementation PR to merge. Explicit starts show unmet needs
as advice and keep the normal feature gates.

Review the plan PR's parts and contracts. The coffee plan has `server-1`,
`phone-1`, `barista-1`, then `journeys`. The phone never talks directly to the
barista screen. Each part tests other parts as fakes from their contracts.
A feature run reads the map and contracts and does not change `contracts/`.

## Start and track runs

After the plan PR is merged and its base branch is available locally:

```sh
pdd product next
pdd product start server-1 --agent codex
pdd product start phone-1 --no-run
pdd product status
pdd product status --json
```

The first three coffee runs have the same needs and can run in parallel. You can
also do them in order with one agent. Start finds the exact run marker in an
existing issue, including closed issues, before making one. `--no-run` only makes
or finds that issue. Each started run keeps the normal feature gates and PRs.

The marker search reads bounded pages, including closed issues. A run belongs
to an issue by a repository owner, member or collaborator, or by you. An
outsider's marker does not claim your run. If trusted duplicates exist, pdd uses
the oldest issue and warns. Long issue titles use a Story count or range; the
body keeps the full IDs and tells the agent how to name the Story files.

Status counts current passing Stories per part and slice, shows stale results,
PRs and what can start next. A stale pass used older files and needs another
check. On another machine, status can read Runtime check lines in the run's PR
and labels those results "from PR #N"; these are not locally verified passes.
Name each Story file with its map id first, for example `P01-menu.md`.
LATER Stories do not count toward planned progress.
No result files are committed, and these commands make no runtime calls.

Only the run's own same-repository PRs count. Status takes check results from the
latest PR with named results, so a code PR without them does not hide the prompt
PR's checks. An implementation merge satisfies a need; a prompt merge does not.
For merged work, current and stale compare with the base branch's files. If
that base is unavailable, status warns and leaves those results unverified.
Needs cycles show their path in status and next. They do not prevent an explicit
start or hide unrelated ready runs.

Journey J1 is the final run after the three parts. Use its normal Story checks
and the whole-product Try to test the path across parts. Status tracks journeys
separately from each part's Stories.

A composed map may navigate directly between parts with a qualified `next.screen`, such as `barista/board`. A target first matches a screen ID local to the current part, even if that local ID contains a slash; otherwise it must name a selected product screen. Select all parts needed by explicit navigation targets. In coffee pickup, Order on the phone opens the barista board; Done returns to the phone, where the background work has made the order Ready.
