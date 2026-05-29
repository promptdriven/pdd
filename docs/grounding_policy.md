# Grounding Policy

`.pdd/grounding_policy.yaml` is an optional, opt-in file that lets a project
require human review and/or pinned examples for critical modules whose
generation depends on PDD Cloud grounding. The policy is consumed by
`pdd/grounding_policy.py` today and is the schema that a future `pdd gate`
check will enforce.

## Schema

```yaml
grounding:
  require_review_for_critical_modules: true
  require_pinned_examples_for:
    - auth
    - payments
    - compliance
```

| Field | Type | Default | Meaning |
| --- | --- | --- | --- |
| `require_review_for_critical_modules` | bool | `false` | When `true`, modules listed in `require_pinned_examples_for` must show `generation.grounding.reviewed == true` in their evidence manifest. |
| `require_pinned_examples_for` | list[str] | `[]` | Module slugs that must include at least one of their own slugs in `generation.grounding.pinned`. |

Module-slug matching is **exact and case-sensitive**. There is no substring
or fuzzy match — `auth_service` does not match `auth`.

## How it's evaluated

`pdd.grounding_policy.check(policy, module, grounding)` returns a list of
`PolicyViolation` records:

| Code | Severity | Triggers when |
| --- | --- | --- |
| `grounding.review_required` | `error` | Policy requires review, module is critical, and `grounding.reviewed` is not `true`. |
| `grounding.pin_required` | `error` | Module is critical and its slug is not present in `grounding.pinned`. |
| `grounding.unavailable_for_critical_module` | `warning` | Module is critical but `grounding.mode == "unavailable"` (e.g. local/no-cloud run). |

An empty list means "policy satisfied or not applicable" — the two are
deliberately indistinguishable to callers.

## Local / no-cloud mode

When the run had no cloud grounding available, the evidence manifest records
`generation.grounding.mode = "unavailable"` rather than failing. The policy
emits `grounding.unavailable_for_critical_module` (warning) for critical
modules in that state, so CI can surface the gap without blocking purely
offline workflows.

## Relationship to `pdd gate`

`pdd gate` is not yet wired to this policy. The library returns structured
`PolicyViolation` records so the eventual gate integration only has to map
codes → exit policy. Until then, projects can call
`pdd.grounding_policy.check` directly from their own CI scripts.

## Related documents

- `docs/evidence_manifest.md` — schema for `generation.grounding` provenance.
- `docs/prompting_guide.md` — when to pin / exclude / review for critical
  modules.
