# Alpha 0.1.1 checkout testing

1. [Distinguish checkout builds in `2455-version-checkout.md`](2455-version-checkout.md) — a tester can identify a local or branch build by its development version suffix while release output stays stable, with concise instructions for installing, testing, and restoring it.

The previously drafted managed `~/.pdd` development installer, install/select state, and uninstall/restore behavior are obsolete because the planner confirmed that npm local and branch installs already work. Close that scope. Remaining decisions are the branch-name encoding and commit SHA length in the `-dev.<branch>.<sha>` version.
