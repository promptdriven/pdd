# Example scenario: `example-pagination`

A **committed demo scenario** so the whole pipeline (distractor generation →
freeze → materialization → instrumented run → verification → report) can be
exercised end-to-end with **zero model tokens** (mock arm). It is *not* a
pilot scenario — the pilot uses dependency-sliced PDD cores (design §4.1.0).

- **Seeded bug** (`core/src/pager/pagination.py:count_pages`): ceiling
  division written as `(n + d) // d` — correct only when `n % d != 0`.
- **Visible tests** deliberately under-determine the contract (partial last
  page only) → they **pass** on the buggy baseline.
- **Hidden verifier** (`hidden/`, never mounted) checks exact-multiple and
  empty-list cases plus a count-vs-slice consistency sweep → **fails** on
  baseline, **passes** after the oracle edit in `scenario.json`.
- **Pool** — five same-vocabulary modules (filters, sorting, summaries,
  audit, CSV) across `same-package` / `same-layer` / `cross-cutting` tiers.

The baseline expectation (visible pass + hidden fail) is asserted by the
runner before every trial (`check_baseline`), which is the light form of the
design §4.1.2 oracle-equivalence gate.
