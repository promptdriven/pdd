# Research Context (issue #1429)

Research-context deliverables for the **Repo-Bloat Localization Benchmark**
([`../design.md`](../design.md), tracking issue
[#1209](https://github.com/promptdriven/pdd/issues/1209)). This folder answers
the three items of the *Epic: Research Context*
([#1429](https://github.com/promptdriven/pdd/issues/1429)):

| # | Epic item | Deliverable |
|---|-----------|-------------|
| 1 | Literature Review | [`literature-review.md`](literature-review.md) |
| 2 | Potential Ways to Integrate with Existing Studies | [`integration-with-existing-studies.md`](integration-with-existing-studies.md) |
| 3 | Possible Collaborators | [`possible-collaborators.md`](possible-collaborators.md) |

Each item lands as its own sub-PR merged into the parent branch
(`research/1429-research-context`); the parent PR targets `main` and is linked to
[#1429](https://github.com/promptdriven/pdd/issues/1429).

## Source provenance and verification

The existing literature survey for this project lived in a working
spreadsheet. Every source carried over into these documents was independently
verified at its primary source: the **17 arXiv papers were verified against the
authoritative arXiv API** (`export.arxiv.org/api/query`) — title, authors, and
submission date checked one by one — while the one non-arXiv entry, the
**Needle-in-a-Haystack (NIAH) software source, was verified via GitHub** (the
current `github.com/gkamradt/LLMTest_NeedleInAHaystack` redirect). **No source is
unverified, and nothing is fabricated.** Where the spreadsheet used an informal
nickname, the document records the *real* published title and notes the
discrepancy:

| Working nickname | Verified title | arXiv ID |
|------------------|----------------|----------|
| "NoisyBench" | *Lost in the Noise: How Reasoning Models Fail with Contextual Distractors* | [2601.07226](https://arxiv.org/abs/2601.07226) |
| "AGENTS.md paper" | *Evaluating AGENTS.md: Are Repository-Level Context Files Helpful for Coding Agents?* | [2602.11988](https://arxiv.org/abs/2602.11988) |
| "RepoMem / LocAgent" (one row) | **two distinct papers** — *LocAgent: Graph-Guided LLM Agents for Code Localization* ([2503.09089](https://arxiv.org/abs/2503.09089)) and *Improving Code Localization with Repository Memory* ([2510.01003](https://arxiv.org/abs/2510.01003)) | — |

The full verified-source table — title, authors, date, arXiv link, and
verification status — is the first section of
[`literature-review.md`](literature-review.md).
