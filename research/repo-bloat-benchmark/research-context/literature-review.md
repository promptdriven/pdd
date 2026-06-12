# Literature Review — Agentic Localization Degradation Under Repository Bloat

**Epic:** [#1429](https://github.com/promptdriven/pdd/issues/1429) (item 1 — Literature Review)
**Benchmark:** [`../design.md`](../design.md) · tracking issue [#1209](https://github.com/promptdriven/pdd/issues/1209)
**Background companion:** [`../agentic_cli_search.md`](../agentic_cli_search.md)

> **Research question.** Given the same task, model, verifier, and starting code,
> what happens to an agentic code-patching workflow as the surrounding repository
> grows with *plausible-but-irrelevant* files? We measure localization **cost**
> (files/bytes read and tool calls before the first edit), **context-window
> penetration** of distractors, and **hidden-test success** as a function of
> repository bloat held at fixed task semantics.

This review situates that question in the published literature. **Every source
below was independently verified against the authoritative arXiv API** (title,
authors, submission date) before inclusion — see the provenance table in
[`README.md`](README.md). Where this review's figures differ from the project's
earlier working spreadsheet, the spreadsheet number was **not** supported by the
paper's abstract; the verified figure is used and the discrepancy is footnoted.

---

## 1. Verified source table

| # | Verified title | Authors | Date | arXiv / link | Status |
|---|----------------|---------|------|--------------|--------|
| 1 | NoLiMa: Long-Context Evaluation Beyond Literal Matching | Modarressi, Deilamsalehy, Dernoncourt, et al. | Feb 2025 | [2502.05167](https://arxiv.org/abs/2502.05167) | ✅ verified |
| 2 | LongBench: A Bilingual, Multitask Benchmark for Long Context Understanding | Bai et al. | Aug 2023 | [2308.14508](https://arxiv.org/abs/2308.14508) | ✅ verified |
| 3 | Needle-in-a-Haystack pressure test | G. Kamradt | 2023 | [GitHub](https://github.com/gkamradt/LLMTest_NeedleInAHaystack) | ✅ verified (software, not arXiv) |
| 4 | LOCA-bench: Benchmarking Language Agents Under Controllable and Extreme Context Growth | Zeng, Huang, He | Feb 2026 | [2602.07962](https://arxiv.org/abs/2602.07962) | ✅ verified |
| 5 | Lost in the Noise: How Reasoning Models Fail with Contextual Distractors | Lee, Jo, Seo, Lee, Seo | Jan 2026 | [2601.07226](https://arxiv.org/abs/2601.07226) | ✅ verified — *spreadsheet "NoisyBench"* |
| 6 | SWE-bench: Can Language Models Resolve Real-World GitHub Issues? | Jimenez, Yang, et al. | Oct 2023 | [2310.06770](https://arxiv.org/abs/2310.06770) | ✅ verified |
| 7 | Agentless: Demystifying LLM-based Software Engineering Agents | Xia, Deng, Dunn, Zhang | Jul 2024 | [2407.01489](https://arxiv.org/abs/2407.01489) | ✅ verified |
| 8 | FeatBench: Towards More Realistic Evaluation of Feature-level Code Generation | Chen, Li, Li | Sep 2025 (v2 Feb 2026) | [2509.22237](https://arxiv.org/abs/2509.22237) | ✅ verified |
| 9 | RepoMod-Bench: A Benchmark for Code Repository Modernization via Implementation-Agnostic Testing | Li, Ben-Israel, Raz, Ahmed, Serebro, Raux | Feb 2026 | [2602.22518](https://arxiv.org/abs/2602.22518) | ✅ verified |
| 10 | RepoBench: Benchmarking Repository-Level Code Auto-Completion Systems | Liu, Xu, McAuley | Jun 2023 | [2306.03091](https://arxiv.org/abs/2306.03091) | ✅ verified |
| 11 | CrossCodeEval: A Diverse and Multilingual Benchmark for Cross-File Code Completion | Ding et al. | Oct 2023 | [2310.11248](https://arxiv.org/abs/2310.11248) | ✅ verified |
| 12 | LocAgent: Graph-Guided LLM Agents for Code Localization | Chen et al. | Mar 2025 | [2503.09089](https://arxiv.org/abs/2503.09089) | ✅ verified — *introduces Loc-Bench* |
| 13 | Improving Code Localization with Repository Memory | Wang, Xu, Li, Gao, Xie, Sun, Chen | Oct 2025 | [2510.01003](https://arxiv.org/abs/2510.01003) | ✅ verified — *spreadsheet "RepoMem"* |
| 14 | CodeSearchNet Challenge: Evaluating the State of Semantic Code Search | Husain et al. | Sep 2019 | [1909.09436](https://arxiv.org/abs/1909.09436) | ✅ verified |
| 15 | CoSQA: 20,000+ Web Queries for Code Search and Question Answering | Huang et al. | May 2021 | [2105.13239](https://arxiv.org/abs/2105.13239) | ✅ verified |
| 16 | CodeXGLUE: A Machine Learning Benchmark Dataset for Code Understanding and Generation | Lu et al. | Feb 2021 | [2102.04664](https://arxiv.org/abs/2102.04664) | ✅ verified |
| 17 | Evaluating AGENTS.md: Are Repository-Level Context Files Helpful for Coding Agents? | Gloaguen et al. (ETH SRI Lab) | Feb 2026 | [2602.11988](https://arxiv.org/abs/2602.11988) | ✅ verified — *spreadsheet "AGENTS.md paper"* |
| 18 | SlopCodeBench: Benchmarking How Coding Agents Degrade Over Long-Horizon Iterative Tasks | Orlanski, Roy, Yun, et al. | Mar 2026 | [2603.24755](https://arxiv.org/abs/2603.24755) | ✅ verified |

*Author lists are abbreviated where long; full lists are on each arXiv page.*

---

## 2. Static long-context degradation — the theoretical motivation

The foundational result motivating this work is that LLM accuracy falls as
**total context grows, even within the advertised window**.

- **NoLiMa** [1] extends the needle-in-a-haystack paradigm by removing literal
  lexical overlap between question and "needle," forcing latent-association
  retrieval. Across 13 models claiming ≥128K support, performance is strong
  below ~1K tokens but degrades sharply with length: at 32K, 11 of 13 models
  drop below 50% of their short-context baseline, and even GPT-4o falls from a
  99.3% baseline to 69.7%. The authors attribute the decline to the attention
  mechanism's difficulty without literal anchors.
- **LongBench** [2] establishes the bilingual, multitask long-context evaluation
  norm, and the **needle-in-a-haystack** pressure test [3] is the widely used
  informal probe that NoLiMa formalizes and hardens.

**Gap for our design.** These studies use synthetic or document-retrieval tasks,
not software repositories or coding agents, and none instrument *file-level agent
search behavior* as the causal mechanism. They justify *why* bloat should hurt;
they do not measure localization cost in code.

---

## 3. Dynamic context growth in agentic settings — the closest design analogue

- **LOCA-bench** [4] is the nearest methodological relative. It holds task
  semantics fixed while using "automated and scalable control of environment
  states to regulate the agent's context length," extending context "potentially
  to infinity in a controlled way." It evaluates agents as *(model × scaffold)*
  combinations and reports that performance generally degrades as environment
  state grows, while context-management strategies can substantially recover
  success. The project is from HKUST-NLP (`github.com/hkust-nlp/LOCA-bench`).

  *Distinction.* LOCA-bench operates on general agentic tasks (its abstract does
  not commit to the specific "halves from 8K→256K" or per-model rankings recorded
  in our earlier spreadsheet[^loca]). It does **not** inject source-code
  distractors, instrument filesystem reads, or measure `files_read` /
  `bytes_read` before first edit. Our contribution is the *software-repository +
  filesystem-instrumented + localization-cost* combination. The shared "keep the
  task fixed, scale the noise variable" principle should be cited explicitly as
  prior art in our Related Work.

- **Lost in the Noise** [5] (the spreadsheet's "NoisyBench") systematically
  injects distractors — random documents, irrelevant chat history, and *hard
  negatives* — across 11 datasets spanning RAG, reasoning, alignment, and
  tool-use. It reports a **catastrophic drop of up to 80%**, finds that agentic
  workflows *amplify* errors by over-trusting noisy tool outputs, and uncovers an
  **inverse-scaling** trend (more test-time compute → worse under noise), with
  attention visualizations showing models fixate on distractor tokens.

  *Distinction.* Document-level distractors, not source files; no LOC scaling, no
  filesystem instrumentation, no bug-localization task. Its hard-negative finding
  directly motivates our **same-package distractor tier** being the most harmful,
  and its attention finding is the mechanistic hypothesis our per-tier
  `irrelevant_file_read_ratio` tests *in code*.

[^loca]: The earlier working spreadsheet recorded "agent accuracy halves as
    context grows from 8K to 256K" and "Claude-4.5-Opus best at short context."
    Those specifics are **not** stated in the verified LOCA-bench abstract and are
    omitted here pending confirmation against the paper body.

---

## 4. Repository-level coding-agent evaluation — the task precedent

- **SWE-bench** [6] established real-repository bug-fixing as a meaningful task
  and the hidden-test evaluation norm: 2,294 problems from 12 Python repos. At
  publication the best model (Claude 2) resolved only 1.96%; the leaderboard has
  since risen dramatically on the Verified subset, which is itself evidence that
  the task is now tractable enough to study *second-order* effects like bloat.
- **Agentless** [7] shows a deliberately simple three-phase
  *localization → repair → validation* pipeline (no autonomous tool loop) reaches
  32.00% on SWE-bench Lite at ~$0.70/instance, and — importantly for us — its
  authors manually found SWE-bench Lite issues with leaked ground-truth patches
  or misleading descriptions, producing the cleaned **Lite-S**. This is direct
  precedent for our **seed-novelty audit** (a distractor or oracle patch must not
  be an upstream-code restoration).

**Gap for our design.** Repository size is *uncontrolled* across SWE-bench issues
and success/fail is the only first-class metric. Agent *search cost* (files read,
bytes read, tool calls before first edit) is at most incidental tool-call data in
agent papers. We make it the primary measurement target.

---

## 5. Repository size vs. agent success — observational evidence

Two recent benchmarks provide the strongest observational signal that scale hurts
coding agents:

- **FeatBench** [8] evaluates feature implementation from natural-language
  requirements only (no code hints), with an evolving anti-contamination
  pipeline (157 tasks, 27 repos). The highest resolved rate is only **29.94%**,
  and the dominant failure mode is "aggressive implementation" causing **scope
  creep and regressions** — agents break existing features by over-reaching.[^feat]
- **RepoMod-Bench** [9] benchmarks repository modernization with an
  implementation-agnostic, hidden test suite (21 repos, 8 languages, 1.6M LOC,
  11,616 tests; repo sizes 14–211K LOC). It reports a **sharp scaling collapse:
  average pass rate drops from 91.3% on projects under 10K LOC to 15.3% on
  projects exceeding 50K LOC**.

**Gap for our design.** Both are *observational* — different repositories with
different tasks, so repo size is confounded with task difficulty. Neither holds
the bug constant while injecting distractor files, and neither measures
localization cost. Their degradation magnitudes are valuable for sanity-checking
our pre-registered practical thresholds (design §7.5), and our controlled design
is the causal follow-on that explains them.

[^feat]: The earlier spreadsheet recorded a "60–70% (small repos) → 10–30%
    (large repos)" breakdown. That split is not in the verified FeatBench
    abstract; only the 29.94% top resolved rate and the scope-creep finding are
    cited here.

---

## 6. Cross-file context, localization accuracy, and code search

- **RepoBench** [10] and **CrossCodeEval** [11] show single-file benchmarks
  understate difficulty: models must retrieve relevant cross-file context. They
  motivate localization as a core sub-problem but evaluate *completion quality*,
  not localization *efficiency*, and do not vary repo size.
- **LocAgent** [12] introduces graph-guided localization (codebase → directed
  heterogeneous graph) and the **Loc-Bench** evaluation set. **Improving Code
  Localization with Repository Memory** [13] (the spreadsheet's "RepoMem") adds a
  commit-history / linked-issue memory on top of LocAgent and improves
  Accuracy@k on SWE-bench-Verified and SWE-bench-live.

  *Distinction.* Both measure localization **accuracy** (was the right file
  found?), not localization **cost** (how much was read before finding it?), and
  neither varies repo size as an independent variable. Our
  `files_read_before_first_edit` is absent from both. **Note:** the earlier
  spreadsheet collapsed these into one "RepoMem / LocAgent" row; they are *two
  distinct papers* and are separated here.
- **CodeSearchNet** [14], **CoSQA** [15], and **CodeXGLUE** [16] ground semantic
  code retrieval and precision@k baselines — the retrieval analogue of our
  `irrelevant_file_read_ratio` — but study retrieval decoupled from end-to-end
  patching and do not control distractor density.

---

## 7. Adjacent phenomena: context-file overhead and iterative degradation

- **Evaluating AGENTS.md** [17] (ETH SRI Lab) is the closest *direct* evidence
  that more repository context can *hurt* coding agents: across multiple agents
  and LLMs, context files tend to **reduce** task success versus no context while
  **inflating inference cost by over 20%**, partly by encouraging broader
  exploration/testing. It studies *instruction* files, not file-count growth, but
  empirically supports the "more context = noise" hypothesis our work isolates.
- **SlopCodeBench** [18] measures degradation as agents iteratively extend *their
  own* solutions (36 problems, 196 checkpoints, 15 agents). **No agent fully
  solves any problem end-to-end**; the best passes 14.8% of checkpoints;
  structural erosion rises in 77% and verbosity in 75.5% of trajectories; agent
  code is ~2.3× more verbose and ~2.0× more eroded than human repos.[^slop]

  *Distinction.* SlopCodeBench's mechanism is code-quality erosion under
  *self-extension*; ours is localization difficulty under *injected irrelevant
  files*. Related in spirit, distinct in independent variable — a clean
  Related-Work contrast.

[^slop]: The earlier spreadsheet recorded "93 checkpoints," "11 models," and
    "erosion in 80% of trajectories." The verified abstract states 196
    checkpoints, 15 agents, and erosion/verbosity in 77% / 75.5% of trajectories;
    the verified figures are used here.

---

## 8. Where the gap is — our contribution

Mapping the field onto our design surfaces three genuine, defensible gaps:

1. **A *controlled* repo-bloat experiment with LOC as the sole independent
   variable.** No prior benchmark holds the target bug constant and scales
   *irrelevant* file volume at 1×/5×/20×/50× by token budget. LOCA-bench and
   *Lost in the Noise* do controlled noise growth in **non-code** domains;
   FeatBench and RepoMod-Bench observe size effects **observationally** in code.
   The controlled-injection-in-a-code-repo cell is empty.

2. **Localization *cost* as a first-class metric.** `files_read`, `bytes_read`,
   `search_calls`, and `input_tokens_*` split at the first-edit boundary, plus the
   FS-tap + transcript-tap dual instrumentation (design §6), are not the primary
   target of any prior coding-agent benchmark — at most incidental tool-call
   counts (SWE-agent, Agentless).

3. **Distractor-tier analysis** (same-package vs. same-layer vs. cross-cutting)
   and a **pre-registered practical-threshold** verdict (≥2× cost rise, ≥0.20
   irrelevant-read-ratio rise, ≥20 pp hidden-pass-rate drop). *Lost in the Noise*
   uses hard-negative vs. random distractors in documents; the spatial/architectural
   proximity taxonomy in source code, and the pre-registered thresholds-not-p-values
   verdict, are original here.

These gaps — and the per-study integration tactics that exploit them — are
developed in [`integration-with-existing-studies.md`](integration-with-existing-studies.md).

---

## 9. References

All entries verified against `export.arxiv.org/api/query` on 2026-06-12.

1. Modarressi et al. *NoLiMa: Long-Context Evaluation Beyond Literal Matching.* arXiv:2502.05167.
2. Bai et al. *LongBench: A Bilingual, Multitask Benchmark for Long Context Understanding.* arXiv:2308.14508.
3. Kamradt. *LLMTest_NeedleInAHaystack.* https://github.com/gkamradt/LLMTest_NeedleInAHaystack.
4. Zeng, Huang, He. *LOCA-bench: Benchmarking Language Agents Under Controllable and Extreme Context Growth.* arXiv:2602.07962.
5. Lee, Jo, Seo, Lee, Seo. *Lost in the Noise: How Reasoning Models Fail with Contextual Distractors.* arXiv:2601.07226.
6. Jimenez, Yang et al. *SWE-bench: Can Language Models Resolve Real-World GitHub Issues?* arXiv:2310.06770.
7. Xia, Deng, Dunn, Zhang. *Agentless: Demystifying LLM-based Software Engineering Agents.* arXiv:2407.01489.
8. Chen, Li, Li. *FeatBench: Towards More Realistic Evaluation of Feature-level Code Generation.* arXiv:2509.22237.
9. Li et al. *RepoMod-Bench: A Benchmark for Code Repository Modernization via Implementation-Agnostic Testing.* arXiv:2602.22518.
10. Liu, Xu, McAuley. *RepoBench: Benchmarking Repository-Level Code Auto-Completion Systems.* arXiv:2306.03091.
11. Ding et al. *CrossCodeEval: A Diverse and Multilingual Benchmark for Cross-File Code Completion.* arXiv:2310.11248.
12. Chen et al. *LocAgent: Graph-Guided LLM Agents for Code Localization.* arXiv:2503.09089.
13. Wang et al. *Improving Code Localization with Repository Memory.* arXiv:2510.01003.
14. Husain et al. *CodeSearchNet Challenge: Evaluating the State of Semantic Code Search.* arXiv:1909.09436.
15. Huang et al. *CoSQA: 20,000+ Web Queries for Code Search and Question Answering.* arXiv:2105.13239.
16. Lu et al. *CodeXGLUE: A Machine Learning Benchmark Dataset for Code Understanding and Generation.* arXiv:2102.04664.
17. Gloaguen et al. *Evaluating AGENTS.md: Are Repository-Level Context Files Helpful for Coding Agents?* arXiv:2602.11988.
18. Orlanski et al. *SlopCodeBench: Benchmarking How Coding Agents Degrade Over Long-Horizon Iterative Tasks.* arXiv:2603.24755.
