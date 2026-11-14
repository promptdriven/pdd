# See an area agent launch failure

As a developer starting a feature run, I want to see when its area agent exits during startup, so that I can inspect the failure and restart the chat.

## Acceptance criteria

1. When the story chat for run 2634 fails to start with exit status 1, `pdd workflow status 2634` reports the failure and exit status 1 and gives `pdd workflow open 2634 --new` as the recovery command.

## What must not change

- An agent positively observed running still appears as working.
- A missing or unreadable observation alone does not prove a launch failed.

## Rules to check

- Only an exit belonging to the current fresh launch can establish its failure. Forbidden: an old or malformed receipt fails a newer launch.
- A pane launch acknowledgement alone does not establish that the agent works. Forbidden: a working claim before positive observation.
- Terminal output is not captured in the saved failure. Forbidden: persisting the agent's terminal output or raw error text.
