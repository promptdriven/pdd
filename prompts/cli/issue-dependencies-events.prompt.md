# Optional signed dependency event hints

Own `src/issue-dependencies-events.mjs`. Export module functions
`acceptDependencyEvent({repository,delivery,event,body,signature},ports)` and
`dependencyEventStatus({configured,installed,verified,error})`.
This adapter accepts an already configured receiver's raw body. It installs no
receiver, hook, daemon, public host, secret or cloud service. Default is disabled.

Verify the exact raw bytes with injected `signature.verify({body,signature})`
before parsing or accepting an event. The default uses GitHub's HMAC-SHA256 scheme
and constant-time comparison; missing secret, malformed signature and mismatch
reject without state changes. Cryptographic correctness needs native verification.
Allow issues, issue_dependencies, issue_comment and pull_request hints only for
the configured repository or a known full prerequisite issue identity from
`scope.read({repository})`, which returns `{issues}`. Repository membership alone
is insufficient for a foreign event: establish its affected issue key from the
native payload or leave it out of scope. A root-repository event may be a hint
without identifying a linked issue. Untrusted payload text never becomes an instruction.

Use `events.read({repository})`/`events.save({repository,json})` for bounded delivery
ID deduplication and pending hints. Machine reasons are signature (invalid verification), scope (foreign repository),
unsupported (unhandled event), duplicate (already accepted), queued (durably queued),
and pending (delivery could not be queued). Only queued has accepted true.
A duplicate returns accepted false, reason duplicate. A new accepted hint calls `reconcile.hint({repository,delivery})`, which
only queues the intake owner's same reconciliation path. Do not apply the event's
old issue state. Reconciliation rereads current GitHub, so a delayed close cannot
undo a reopen. A failed/busy hint stays pending; mark accepted delivery only when
queued durably. Suppress unchanged PDD bookkeeping wakeups through that owner.
Polling remains active regardless of webhook absence or failure.

Status returns the four supplied observations separately and a state: disabled
when not configured; configured when configured but not installed or not verified;
active only when configured, installed and delivery-verified; degraded when a
configured adapter has an error. Local signature tests prove no installed hook or
successful live delivery. Never infer installed or verified from configuration.

## Dependencies

- [Intake reconciliation](issue-dependencies-intake.prompt.md): required generation,
  runtime and verification context for the single canonical reread path.

<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"82aa5a3ba9fbf6039b15df604d0c8d51fd8fcc4053654e3b05bd0099ce57b7ff","entries":[{"operation":"acceptDependencyEvent","input_schema":{"type":"object","properties":{"repository":{"type":"string"},"delivery":{"type":"string"},"event":{"type":"string"},"body":{"type":"string"},"signature":{"type":"string"}},"required":["repository","delivery","event","body","signature"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"accepted":{"type":"boolean"},"reason":{"type":"string","enum":["signature","scope","unsupported","duplicate","queued","pending"]}},"required":["accepted","reason"],"additionalProperties":false},"errors":[]},{"operation":"dependencyEventStatus","input_schema":{"type":"object","properties":{"configured":{"type":"boolean"},"installed":{"type":"boolean"},"verified":{"type":"boolean"},"error":{"type":"string"}},"required":[],"additionalProperties":false},"result_schema":{"type":"object","properties":{"state":{"type":"string","enum":["disabled","configured","active","degraded"]},"configured":{"type":"boolean"},"installed":{"type":"boolean"},"verified":{"type":"boolean"}},"required":["state","configured","installed","verified"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[{"name":"signature","kind":"port","access":"read","operations":[{"name":"verify","access":"read","arguments_schema":{"type":"object","properties":{"body":{"type":"string"},"signature":{"type":"string"}},"required":["body","signature"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"valid":{"type":"boolean"}},"required":["valid"],"additionalProperties":false}}]},{"name":"scope","kind":"port","access":"read","operations":[{"name":"read","access":"read","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"}},"required":["repository"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"issues":{"type":"array","items":{"type":"string"}}},"required":["issues"],"additionalProperties":false}}]},{"name":"events","kind":"port","access":"write","operations":[{"name":"read","access":"read","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"}},"required":["repository"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"json":{"type":"string"}},"required":["json"],"additionalProperties":false}},{"name":"save","access":"write","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"},"json":{"type":"string"}},"required":["repository","json"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"ok":{"type":"boolean"}},"required":["ok"],"additionalProperties":false}}]},{"name":"reconcile","kind":"port","access":"write","operations":[{"name":"hint","access":"write","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"},"delivery":{"type":"string"}},"required":["repository","delivery"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"ok":{"type":"boolean"}},"required":["ok"],"additionalProperties":false}}]}],"limits":{"max_steps":30,"max_model_calls":12},"conventions":[]}
```
</details>
