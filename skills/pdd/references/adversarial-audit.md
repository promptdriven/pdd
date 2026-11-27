# Adversarial & External-Premise Audit

`pdd test`, frozen vector replays, and code-bound formal checks prove **internal consistency** (`code == prompt == hand-derived expectations`). They cannot prove **external validity** — whether the prompt's domain premises, baselines, external constants, and incentive or threat model hold outside its own fixtures.

Run this audit as a distinct prompt-space stage **before investing in full code-space build** (and separately from Story-vs-Prompt consistency review).

## 1. When to run vs. skip (`not-applicable`)

- **Run** before prompt approval or codegen whenever a prompt encodes:
  - pricing, billing, fee, auction, quota, scheduling, or resource-allocation models;
  - authentication, authorization, multi-tenant isolation, settlement/escrow, or security trust boundaries;
  - analytical, economic, or benchmark models claiming improvement over a baseline;
  - stateful multi-party protocols, external MCP/CLI tool surfaces, or OS/cross-host boundaries (clocks, permissions, redaction patterns, third-party CLI limits).
- **Skip as `not-applicable`** (zero ceremony) on documentation, UI copy/layout/styling, simple single-tenant CRUD, or internal refactors with no external premises or incentive surfaces.

## 2. Independence rule (no circular self-verification)

Do not rely solely on the same agent session that researched external assumptions, wrote scratch scripts, generated test vectors, and checked the prompt against those vectors. Run the audit in a **clean-context independent challenger pass** (given only the prompt, Stories, linked contracts, and cited source artifacts — zero author chat history).

For multi-tool MCP or CLI surfaces, pair the challenger pass with a **blind external client probe**: give a fresh client zero repo access so it discovers operations strictly through live MCP `tools/list` / `resources/list` or CLI `--help`, catching schema discoverability gaps, cross-store drift, unresolved template placeholders, and data-leak paths.

## 3. Four-part audit checklist

### 1. Abuse, incentive, and arbitrage invariants
- Can an adversarial caller game the contract by **relabeling, splitting, batching, reordering, or replaying** inputs (for example, relabeling a request class to pay less, smuggling unvalidated parameters, or spoofing a caller role)?
- On stateful security or economic prompts, test whether multi-step sequences can break isolation or conservation (cross-tenant key collisions, balance underflow/minting, unilateral settlement without stored consent, stale-epoch cleanup, or lockout/accounting regressions introduced by earlier fixes).
- Pair static review with **live stateful adversarial probing** (`try_run` or direct `pdd <STORY>` exploration across unhappy paths and multi-step state transitions) before codegen, and re-probe after major remediation fixes.

### 2. Naive baseline fairness
- Does the design's claimed benefit (cost, latency, throughput, accuracy, or utilization) survive comparison against the **simplest naive baseline** (such as a static 2-tier schedule, fixed cap, or simple threshold)?
- Challenge synthetic workloads or hand-crafted demand assumptions that vanish once evaluated against a plain baseline.

### 3. External constant provenance & environmental premises
- **Pinned constants:** Every hardcoded external figure (competitor prices, rate cards, hardware throughput multipliers, parameter counts, API quotas, or limits) must point to a **pinned, timestamped source artifact** (repo file, rate card, or linked spec) rather than model memory.
- **Hidden environment and boundary premises:** Enumerate assumptions that unit mocks and prompt fixtures hide:
  - **Clocks:** cross-host clock skew (never implicitly assume one shared clock).
  - **OS and filesystem defaults:** Linux vs. macOS differences (for example Linux User Private Group `0775`/`0664` default permissions, path casing, symlink handling, and third-party CLI output sizes).
  - **Pattern anchoring:** unanchored redaction or validation regexes that collide with ordinary multi-segment IDs or valid inputs.
  - **Cross-layer ownership:** ask *"Does this rule depend on fields, omitted-optional-flag defaults, caller-session checks, or enclosing audit hooks that are absent from this operation's declared inputs or ports?"*

### 4. Falsification / kill criteria
- Record at least one concrete real-world measurement, live probe, or quantitative threshold that would **invalidate or kill the design** before investing in full code-space build (for example, *"if a 2-tier static baseline stays within 5% on real workload traces, drop the dynamic tier"* or *"verify live token validation under ±60 s cross-host clock skew"*).

## 4. Concise output format

Keep findings advisory, concrete, and anchored to exact `file:line` references (zero brittle regex gates):

```markdown
### Adversarial / External-Premise Audit
- **Applicability:** Applicable | Not applicable (<short reason>)
- **Findings:**
  1. **[Abuse | Baseline | Provenance | Boundary] `<file>:<line>`** — <concrete premise gap or exploit path>
     - **Challenge / fix:** <1-sentence fence, pinned source, or boundary clarification>
- **Falsification / kill criteria:** <concrete real-world test or threshold before full code build>
```

If applicable and zero blockers survive challenge, record: `No external-premise blockers found` alongside the falsification criteria.
