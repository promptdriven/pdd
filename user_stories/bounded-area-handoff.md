# Keep earlier-area handoffs bounded and recoverable

As a person running PDD, I want later area chats to receive bounded previews of earlier step summaries, so that a large saved summary cannot expand every later brief without limit.

Source inspection identifies unbounded summary copying; it does not establish historical model savings or a complete reproduction of issue #2795.

## Acceptance criteria

1. A later area keeps completed earlier steps in workflow order. Short summaries keep their current one-line text and empty summaries still show "done"; incomplete and current-area steps are excluded.
2. Each displayed step item, including its step label and shortening marker, uses at most 1,024 UTF-8 bytes. An oversized item keeps the longest complete-code-point prefix that fits before " … [summary shortened; read ledger]"; Unicode characters remain valid.
3. The entire "Approved so far:" line, including labels, separators, markers and its final period, uses at most 8,192 UTF-8 bytes. It keeps the longest leading sequence of capped items that fits and reports the exact remaining count as "[N further step summaries omitted; read ledger]".
4. Any shortened or omitted summary has one clear recovery instruction outside that line. It gives the exact original status.json path and full-summary selector under "done", warns that previews are incomplete, and requires full evidence before relying on a shortened or omitted result, check/approval claim, unresolved failure or decision.
5. The original saved summaries, line breaks, decisions, approvals, reports, gates, pending questions and completed-step records stay intact. A bounded preview grants no approval, changes no role or workflow progress, and does not change PR or status rendering.

## Rules to check

The per-item and aggregate limits count UTF-8 bytes, not characters or tokens. Equality fits without shortening. For aggregate overflow, reserve the omission marker and keep whole capped items in order; never skip a large item to show a later one. Forbidden: exceeding either cap, cutting a code point, silently omitting evidence, changing durable records, or treating previews as approval or a passing result.

## Evidence and verification boundary

Owner: [workflow runner](../prompts/cli/workflow-runner.prompt.md#bounded-earlier-area-summaries). Cases: [native/manual case manifest](../test/authoring-guidance/bounded-area-handoff-cases.json).

The existing partial Runtime interface does not expose area-chat brief creation. This manifest is not an executable Runtime scenario. Prompt tests: NOT RUN. Native/manual cases: NOT RUN. Implementation has not changed. Native tests must call the real approval/open recovery boundary with temporary run storage and injected Herdr/program ports, inspect the delivered start brief, and compare the saved ledger. Manual review must check that recovery advice identifies full failures, decisions and report paths. No model-token, latency or cost savings are proved.

## Recovery fallback

The worker must read all earlier summaries if it cannot safely identify the needed subset; that fallback can restore the original context load.
