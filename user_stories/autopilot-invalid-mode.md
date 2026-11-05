# Replace an invalid mode

As a repository maintainer, I can replace an invalid saved mode, so that the setting is usable again.

## Acceptance criteria

1. Setup treats saved invalid mode turbo as off and leaves it unchanged.
2. Running `pdd autopilot auto` replaces saved invalid mode turbo with auto.

## Rules to check

- Native test: repeat with nonstring saved modes and confirm the notice and disk preservation.
