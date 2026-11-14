# Read all workflow status as JSON

As a person who steers runs from a phone, I want a versioned JSON list of my runs, so that my service can show what needs attention.

## Acceptance criteria

1. `pdd workflow status --all --json` with no runs returns version 1 and an empty runs list.

## Rules to check

- Each run identifies its issue, workflow, agent, current area and step, PRs, Story count, chat location and last change.
- Waiting reports the gate, question, stopped chat or startup failure; a stopped chat reports its reason or unknown.
- The JSON never includes a private Try link.
