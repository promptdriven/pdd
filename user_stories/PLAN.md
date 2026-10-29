# Alpha 0.1.1 checkout installer

1. [Install and select a checkout build](2455-install-checkout.md) — a tester can install a checkout build into the managed layout, select it, and see its development version.
2. [Uninstall and restore the previous selection](2455-uninstall-checkout.md) — a tester can remove that development installation and recover the active state that preceded it.

Open questions for approval: the exact command and arguments; the authoritative `runtime.json` and active-selection schema; artifact and Node-tool copy rules; version source and `-dev` spelling; supported OS/Node/permissions; idempotence and behavior when another installation becomes active.
