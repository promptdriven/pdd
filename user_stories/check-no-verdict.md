# Recognize checks with no verdict

I can distinguish a failed check from a check that got no verdict, so I can follow the reported next step.

## Acceptance criteria

1. Refused, nonbusy not-run and unknown checks say "no verdict" instead of a cross on Story and overall summary lines.
2. A failed check keeps the cross even when another check has no verdict; all passed checks keep the tick.
3. Queued or running checks keep "running" when none failed; "busy" appears only when every row is busy, and busy cannot hide another no-verdict check.

4. JSON keeps a refused check's refusal cause and the server explanation and next step on refused, not-run and unknown checks.

## Rules to check

A cross requires a judged failed check. Marks follow failed, all-passed, open, only-busy, then no-verdict precedence. Story and overall lines share this rule. Changing exit codes, claiming a refusal passed, and hiding unknown/refused rows behind busy are forbidden.

## What must not change

Exit precedence, check and criterion counts, call accounting, draft labels and report links remain unchanged. Server explanations and next steps take precedence as owned by the runtime output prompt; deterministic client tests separately prove projection, text, mixed-exit notices and JSON.
