# Keep workflow progress when commands overlap

I can finish workflow work while another workflow command is still running,
without losing the progress either command successfully records.

## Acceptance criteria

1. When an earlier status refresh, step completion or question command saves after newer unrelated work was recorded, that newer work remains saved, including completed steps, questions, gates, decisions, area progress and PR fields.
2. When two overlapping commands successfully record different unrelated steps, both steps remain saved; sequential completions retain both steps too.
3. Running a completed step again still clears later known steps of its own area, including a later step added or replaced while the command was running; unrelated steps remain saved.
4. Asking a question saves that requested question, and refreshing status saves the actual refreshed CI result, while each command retains unrelated newer progress.
5. Ordinary progress saves leave accepted change requests, delivery state and acknowledgement time and note unchanged; existing warning-only uptake visibility and approval rules still apply.
6. A command selected for an older run cannot change a replacement run at the same location, and a failed progress save ends with a clear failure rather than claiming it was saved.

## Rules to check

A successful stale save must not erase unrelated durable work. Both successful
unrelated concurrent completions must survive. Intentional rerun invalidation is
limited to later known steps of that area; retaining those stale later results
is also wrong. A newly asked question and a genuinely refreshed CI result must
take effect. An older completion must not clear a question asked independently
after it loaded. A replaced run must remain unchanged by the older command.
No additional step-order or approval gate is introduced.

## Native checks

Requirement-derived cases: [native case inventory](../test/workflow-concurrent-progress/cases.json).
The checks use the actual public workflow commands, private scratch Git/HOME
and injected external effects. Worker barriers exercise overlapping native
record saves. The synchronous production update callback and native filesystem
ownership are unbound to the Interpreter; this inventory is data, not an
Interpreter scenario, execution report or proof that the implementation passes.
