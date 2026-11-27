# Abuse and adversary review checklist (`abuse`)

Check prompts that touch ports, auth/trust, money/pricing, security, or `kind: native-only` boundaries for exploitable loopholes.

## What to flag

1. **Arbitrage and relabeling loopholes:** Splitting, reordering, replaying, rounding, negative or zero amounts, currency or unit confusion, or relabeling inputs to evade caps, fees, quotas, discounts, or idempotency.
2. **Caller-trusted auth, identity, or clocks:** Accepting caller-supplied roles, tenant IDs, timestamps, signatures, or override flags without trusted port verification, or failing open when credentials expire or are missing.
3. **Injection, coercion, and path or encoding tricks:** Symlink traversal, `.git` or case-sensitivity bypasses, command, SQL, header, or template injection, control characters, or type coercion (`"0"`, `null`, `NaN`, arrays) defeating a guard.
4. **Cross-tenant or secret leaks:** Exposing another tenant data, leaking tokens or credentials in errors or logs, or mutating shared state before rejecting an unauthorized call.

## Reporting rules

- Report only concrete, exploitable flaws grounded in an exact verbatim quote from the target file.
- **Executable test idea required:** Every `abuse` finding MUST include a concrete `test_idea` naming the exact adversarial input or call sequence and the expected refusal or invariant so `pdd prove` or a regression test can run it directly.
- Skip generic security advice that does not expose a concrete bug in the quoted rule.
