# Keep an issue for a person

As a person with write access, I want to keep an issue for myself or another team, so that Autopilot does not take work that we handle by hand.

## Acceptance criteria

1. When a person with write access adds `pdd:manual`, Autopilot does not claim, sort or dependency-review the issue. Status lists it once as kept for a person.
2. When that person adds the label to a claimed issue, Autopilot lets the current step finish or save, then releases its claim through the normal release path. The run folder, branch, saved work and PRs stay.
3. Removing the label makes the issue eligible again under the normal rules.
4. An issue author without write access cannot make the label effective, including when that author is on the Autopilot trust list.
5. Installing this capability wakes a run parked for it through the existing capability wake route.
6. The README start path and CLI documentation explain the label and its permission rule.

## Rules to check

- Only a repository owner or a person with write, maintain or admin permission can make the current manual label effective.
- Label removal clears the hold. A later label addition uses the authority of that addition.
- A busy or unobserved worker cannot lose its claim or saved work through manual release.

## Native checks

Run the focused manual-label tests and the manual-label factory scenarios. These tests use disposable Git repositories and the repository service fakes. They do not prove hosted GitHub or live agent behavior.
