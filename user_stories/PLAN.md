# Alpha 0.1.1 checkout testing

1. [Distinguish checkout builds in `pdd --version`](2455-version-checkout.md) — a tester can identify a local or branch build by its development version suffix while release output stays stable.
2. [Document testing a checkout fix before release](2455-test-checkout-docs.md) — a tester can install local/branch npm packages and matching skill branches, then restore the release.

The previously drafted managed `~/.pdd` development installer, install/select state, and uninstall/restore behavior are obsolete because the planner confirmed that npm local and branch installs already work. Close that scope. Remaining decisions are the branch-name encoding and commit SHA length in the `-dev.<branch>.<sha>` version.
