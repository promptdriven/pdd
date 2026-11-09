# Findings native verification

Prerequisites: Node.js 22 and Git. From the repository root, create a disposable directory with `home`, `state`, `config`, and `tmp` subdirectories. Set `HOME`, `XDG_STATE_HOME`, `XDG_CONFIG_HOME`, `TMPDIR`, and `PDD_INTERPRETER_QUEUE` to paths inside it; then run `node --test test/bug-relations/findings.test.mjs`. Remove the disposable directory afterward.

The test creates isolated repositories and invokes the public workflow step with controlled GitHub and relation ports. It reads the approved native case plan and checks persisted findings, malformed intake, retry checkpoints, legacy behavior and inert PR rendering. It does not contact GitHub or prove live mutation, complete PR publication or independent verification.
