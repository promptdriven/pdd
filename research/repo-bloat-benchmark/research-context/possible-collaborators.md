# Possible Collaborators

**Epic:** [#1429](https://github.com/promptdriven/pdd/issues/1429) (item 3)
**Reads with:** [`literature-review.md`](literature-review.md) · [`integration-with-existing-studies.md`](integration-with-existing-studies.md)

> **Scope and honesty note.** Every candidate below is derived **only** from the
> *verified* authorship of a paper already cited in the literature review (all
> arXiv IDs confirmed against `export.arxiv.org` — see [`README.md`](README.md)).
> **No contact details (emails, handles, DMs) are invented in this document.**
> Affiliations are given only where they are well-established or stated by a
> primary source (lab page, project repository); anything else is marked *(confirm)*.
> Treat this as a vetted *starting list for outreach*, not a contact sheet — verify
> each person's current affiliation and preferred contact channel yourself before
> reaching out, ideally via the contact address on the paper itself.

Candidates are grouped by *why* they fit, strongest topical overlap first.

---

## Tier 1 — Closest methodological overlap (controlled context/distractor growth)

### LOCA-bench group — *controlled, infinite context growth at fixed task semantics*
- **Paper:** LOCA-bench (arXiv:[2602.07962](https://arxiv.org/abs/2602.07962)); repo `github.com/hkust-nlp/LOCA-bench`.
- **People:** Weihao Zeng, Yuzhen Huang, **Junxian He** (senior author).
- **Affiliation:** HKUST — the project lives under the `hkust-nlp` org.
- **Why:** They built the closest existing design — hold the task fixed, scale the
  context/noise variable in a controlled way. Our work is the source-code +
  filesystem-instrumented analogue. Natural collaboration on a *shared
  controlled-growth protocol* spanning general-agent and code-repo domains.
- **Outreach angle:** "We extend your fixed-task / controlled-context principle to
  software repositories with filesystem-level localization-cost measurement."

### "Lost in the Noise" group — *distractor robustness, hard negatives, inverse scaling*
- **Paper:** arXiv:[2601.07226](https://arxiv.org/abs/2601.07226).
- **People:** Seongyun Lee, Yongrae Jo, Minju Seo, Moontae Lee, **Minjoon Seo** (senior).
- **Affiliation:** KAIST / LG AI Research *(confirm per author list)*.
- **Why:** Their hard-negative-vs-random distractor taxonomy and attention-fixation
  finding are the document-domain version of our same-package distractor tier and
  per-tier read-ratio. Strong fit for the *mechanistic* (attention-level) side.
- **Outreach angle:** "Your hard-negative distractor effect — does it reproduce in
  source code with architectural proximity tiers? We have the instrumentation."

---

## Tier 2 — Repository-scale coding-agent evaluation

### RepoMod-Bench team — *implementation-agnostic hidden testing; LOC scaling collapse*
- **Paper:** arXiv:[2602.22518](https://arxiv.org/abs/2602.22518); repo `github.com/Modelcode-ai/mcode-benchmark`.
- **People:** Xuefeng Li, Nir Ben-Israel, Yotam Raz, Belal Ahmed, Doron Serebro, Antoine Raux (Modelcode-ai).
- **Why:** They already measured a clean LOC→pass-rate collapse (91.3%→15.3%) and
  built an implementation-agnostic hidden test suite — directly relevant to
  hardening our hidden verifiers and calibrating thresholds.
- **Outreach angle:** "Your observational LOC collapse is what our controlled
  bug-held-constant design aims to causally explain — interested in cross-validation?"

### FeatBench authors — *anti-contamination, evolving real-repo tasks*
- **Paper:** arXiv:[2509.22237](https://arxiv.org/abs/2509.22237).
- **People:** Haorui Chen, Chengze Li, **Jia Li**.
- **Why:** Their evolving-benchmark pipeline (mitigating data leakage) and
  scope-creep failure analysis inform our seed-novelty audit and failure taxonomy.

### SWE-bench / Princeton NLP — *the field's evaluation substrate*
- **Paper:** SWE-bench (arXiv:[2310.06770](https://arxiv.org/abs/2310.06770)).
- **People:** Carlos E. Jimenez, John Yang, Karthik Narasimhan, et al.
- **Affiliation:** Princeton NLP (+ collaborators).
- **Why:** The hidden-test isolation norm we adopt; their SWE-agent ACI work is the
  reference model of agent search primitives. High-visibility validation partner.

### Agentless / Lingming Zhang group — *localization decomposition + ground-truth auditing*
- **Paper:** arXiv:[2407.01489](https://arxiv.org/abs/2407.01489).
- **People:** Chunqiu Steven Xia, Yinlin Deng, Soren Dunn, **Lingming Zhang**.
- **Affiliation:** UIUC *(confirm)*.
- **Why:** Their localization→repair→validation pipeline and manual Lite-S audit are
  the methodological precedent for our seed-novelty audit.

---

## Tier 3 — Code localization & retrieval

### Repository-Memory authors — *state-of-the-art localization accuracy*
- **Paper:** arXiv:[2510.01003](https://arxiv.org/abs/2510.01003).
- **People:** Boshi Wang, **Huan Sun** (OSU NLP); Weijian Xu, Yunsheng Li, Mei Gao,
  Yujia Xie, Dongdong Chen (Microsoft).
- **Why:** They optimize localization *accuracy*; we measure localization *cost*.
  Complementary axes — their memory tool is a natural scaffold variable for an
  extension arm.

### LocAgent / Loc-Bench authors
- **Paper:** arXiv:[2503.09089](https://arxiv.org/abs/2503.09089).
- **People:** Zhaoling Chen, et al.
- **Why:** Loc-Bench instances could seed candidate bug classes; Accuracy@k (theirs)
  vs. cost-before-first-edit (ours) is a clean complementary framing.

---

## Tier 4 — Adjacent phenomena (context overhead, iterative erosion)

### "Evaluating AGENTS.md" — ETH Zurich SRI Lab
- **Paper:** arXiv:[2602.11988](https://arxiv.org/abs/2602.11988); lab page
  `sri.inf.ethz.ch`.
- **People:** Gloaguen et al. (SRI Lab, ETH Zurich).
- **Why:** Their result (repo context files reduce success, +20% cost) is the
  closest direct evidence for "more repo context = noise." Strong co-motivation /
  joint-positioning partner.

### SlopCodeBench — UW–Madison group
- **Paper:** arXiv:[2603.24755](https://arxiv.org/abs/2603.24755).
- **People:** Gabriel Orlanski, Devjeet Roy, … **Frederic Sala**, **Aws Albarghouthi**.
- **Affiliation:** University of Wisconsin–Madison (+ collaborators).
- **Why:** They measure code degradation under self-extension; we measure
  localization degradation under injected files. Complementary "agents degrade as
  repos grow" story — good for a joint survey/position framing.

---

## Outreach checklist (do this per contact)

1. Confirm the person's **current** affiliation and the correct **contact address
   on the paper** (do not reuse anything from this doc as a contact).
2. Lead with the *specific* overlap from the matrix in
   [`integration-with-existing-studies.md`](integration-with-existing-studies.md),
   not a generic ask.
3. Offer the concrete artifact we bring: controlled LOC injection + dual
   FS/transcript instrumentation + pre-registered thresholds.
4. Respect that some candidates are at companies (Modelcode-ai, Microsoft, LG AI
   Research) — collaboration terms differ from academic labs.
5. Keep a log of who was contacted, when, and the response.

*This list intentionally contains no email addresses, phone numbers, or social
handles. All names trace to a verified, cited paper; affiliations marked
*(confirm)* are best-effort and must be checked before use.*
