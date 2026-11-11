# Record intake cards in shadow mode

As a repository maintainer, I can let Autopilot write an intake card for each open issue without changing what it starts, so that I can measure the cards before they decide anything.

## Acceptance criteria

1. After `pdd autopilot start --engine core --intake shadow`, a core tick starts one card job of this machine's agent for each open issue in scope by a trusted author that has no native fact, at most 2 attempts per tick, and saves each valid card with its class, reason, agent and model.
2. The card agent runs in an empty folder with no tools and no write access, never with the bypass flags; an issue by an untrusted author gets no card job, and an untrusted comment never reaches a card.
3. An issue that is assigned, has an open native blocked-by link, has open sub-issues, or carries `pdd:stuck`, `pdd:needs-decision`, `pdd:would-merge` or `pdd:working` gets a native reason and no card job.
4. The same issue version gets no second card job; a new comment, label, assignee, title or body gets one.
5. The core starts the same issues, and makes the same GitHub writes, with intake shadow as with intake off; the intake pass itself writes nothing to GitHub.
6. A card job that ends with no valid card saves an error card and gets no new job for 6 hours unless the issue changes; an error in the pass never stops the tick.
7. A switch to off stops card jobs that still run.
8. `pdd autopilot intake` prints the cards, the would-pick list and today's changes; `--json` prints the same as JSON; `--intake` with another value than `off` or `shadow` exits 2.

## Rules to check

- Native tests drive the core tick with a fake GitHub and a scripted job runner; no real agent, no network.
- The daily change file lists class changes, would-pick changes and the issues that the core really started.
