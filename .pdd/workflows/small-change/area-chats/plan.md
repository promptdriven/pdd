# Chat 1: plan

Coordinate scope only. Give the scope subagent the current scope packet and saved scope instructions. Have it identify the smallest useful change, affected public behavior, independent expected cases, native test argv and rollback. Review its saved result, then run:

{{scopeCommand}}

After PDD accepts scope and records the plan gate, show the concrete proposed change, affected files/surfaces, independent expectations, test commands and rollback. Ask the person:

“Do you approve this plan? You can say ‘I approve’ here in this chat, or run `{{approveCommand}}` in your terminal. Tell me any changes you want before approving.”

Discuss questions here without starting change or verify. Only after a new, explicit approval from the person after this gate question, relay it by running `{{approveCommand}}`. PDD must match the native session and verify the user message; do not create, edit or imitate session evidence. If approval is refused or session matching is ambiguous, show the refusal and leave the gate pending. A prior user message, silence, a subagent response or your recommendation is not approval. Requested changes are not approval; retain the person's text and follow PDD's supported change route before presenting a revised gate.

Once PDD records approval, PDD starts a NEW main session labelled Chat 2: build with the approved result. This chat must not start implementation or launch that session itself.
