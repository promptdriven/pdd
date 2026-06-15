# Literature Review — Agentic Localization Degradation Under Repository Bloat

**Epic:** [#1429](https://github.com/promptdriven/pdd/issues/1429) (item 1 — Literature Review)
**Benchmark:** [`../design.md`](../design.md) · tracking issue [#1209](https://github.com/promptdriven/pdd/issues/1209)
**Background companion:** [`../agentic_cli_search.md`](../agentic_cli_search.md)

> **Research question.** Given the same task, model, verifier, and starting code,
> what happens to an agentic code-patching workflow as the surrounding repository
> grows with *plausible-but-irrelevant* files? We hold task semantics fixed and
> measure localization **cost** (files/bytes read and tool calls before the first
> edit), **context-window penetration** of distractors, and **hidden-test
> success** as a function of repository bloat.

## How to read this review

The field gives us strong reasons to expect repository bloat to hurt agentic
coding — but the evidence is **scattered across three communities that rarely
cite each other**: the long-context community (does accuracy survive a big
window?), the noisy-context / distractor-robustness community (do irrelevant
tokens mislead reasoning?), and the software-engineering-agent community (can an
agent fix a real bug in a real repo?). No single paper sits at their
intersection. This review walks the field in order of *conceptual distance* from
our design — from the abstract motivation (§2) to the closest methodological
relatives (§3) to the code-specific benchmarks (§4–§6) — and ends with the
precise white space we occupy (§8).

**A note on sourcing.** The project's earlier survey lived in a working
spreadsheet. Treating it as unverified, every one of the 18 works below was
checked at its primary source: the **17 arXiv papers were checked against the
authoritative arXiv API** (title, authors, date), while the one non-arXiv
entry — the **Needle-in-a-Haystack (NIAH) software source [3] — was verified via
GitHub** (the current `github.com/gkamradt/LLMTest_NeedleInAHaystack` redirect).
The headline papers were re-read from their full texts so the figures here come from
the papers themselves, not the spreadsheet. Verification corrected several
spreadsheet errors; each correction is footnoted at the point of use. Nothing
here is unverified or fabricated. The provenance summary is in
[`README.md`](README.md).

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

*Author lists are abbreviated where long; full lists are on each arXiv page. Figures cited below are drawn from the papers' own text and tables.*

---

## 2. The motivation: accuracy decays inside the advertised window

The premise underneath this whole project is that an LLM's *effective* context is
smaller than its *nominal* context — adding tokens, even within a 128K+ window,
degrades accuracy. Two results make this concrete.

**NoLiMa** [1] is the sharpest demonstration. The standard needle-in-a-haystack
(NIAH) test [3] is too easy because the "needle" usually shares literal words
with the query, letting attention shortcut to it. NoLiMa removes that crutch: its
needle set is built so questions and needles have *minimal lexical overlap*, so
the model must infer a latent association. Across **13 models that advertise
≥128K context**, performance is near-perfect below ~1K tokens but falls steeply
with length — **at 32K, 11 of the 13 drop below 50% of their own short-context
baseline**, and even GPT-4o, one of the strongest, falls **from a 99.3% baseline
to 69.7%**. The authors trace this to attention struggling to retrieve without
literal anchors. **Why it matters to us:** repository bloat is exactly a
"no-literal-match" haystack — the relevant code does not announce itself, and the
agent must reason its way to it through plausible look-alikes. NoLiMa is the
cleanest evidence that the haystack itself, not just task difficulty, is the
problem. **LongBench** [2] supplies the broader long-context evaluation norm that
NoLiMa hardens.

**What this leaves open:** NoLiMa and LongBench operate on prose/document
retrieval, in a single forward pass, with no agent, no source code, and no
measurement of *what the model did to find the needle*. They tell us bloat should
hurt; they cannot tell us how a coding agent's search loop pays for it.

---

## 3. The closest relatives: controlled growth of the *noise* variable

Two 2026 papers share our core experimental move — **hold the task fixed and turn
a single noise dial** — but in domains other than code repositories. These are
the works we must cite and differentiate most carefully.

### 3.1 LOCA-bench — controlled, near-unbounded context growth for agents

**LOCA-bench** [4] (HKUST-NLP; `github.com/hkust-nlp/LOCA-bench`) is the nearest
methodological relative. Where NoLiMa grows a *static* prompt, LOCA-bench grows
the context an *agent* accumulates: it "leverages automated and scalable control
of environment states to regulate the agent's context length," extending it
"potentially to infinity in a controlled way while keeping the underlying task
semantics fixed." It evaluates agents as *(model × scaffold)* pairs over tool-use
tasks (a Toolathlon-style suite of ~280 tools spanning email, calendar,
BigQuery/Snowflake, spreadsheets, e-commerce, etc.) using a ReAct scaffold.

The degradation is steep and monotone. Sweeping context across **8K → 16K → 32K →
64K → 96K → 128K → 256K**, the paper reports (for example) **Claude-4.5-Opus
falling from 96.0 to 14.7** and **GPT-5.2-Medium from 72.0 to 21.3** over that
range, and the **frontier-vs-open-source gap widens** with length (frontier
models reach roughly 2–3× open-source accuracy at 256K). Crucially, LOCA-bench
shows the decline is *partly recoverable by scaffolding*: context-management
strategies — tool-result clearing, thinking-block clearing, compaction, memory
tools, and especially **programmatic tool calling** — claw back substantial
accuracy (e.g., at 128K, GPT-5.2-Medium 38.7% → 49.3%; DeepSeek-V3.2-Thinking
10.7% → 24.0%).

**Why it matters to us — and how we differ.** LOCA-bench validates the
"one-variable" design we adopt, *and* its scaffold-recovery result is a warning:
our pilot must pin the agent's context-management configuration, or "bloat
sensitivity" will be confounded with scaffold choice. But LOCA-bench grows context
by *injecting environment state into the transcript*; it does **not** inject
*source-code* distractors into a repository, does **not** instrument filesystem
reads, and does **not** measure cost *before the first edit*. The
software-repository + filesystem-instrumented + localization-cost combination is
ours.[^loca]

### 3.2 Lost in the Noise — distractor robustness and inverse scaling

**Lost in the Noise** [5] (the spreadsheet's "NoisyBench") is the distractor-side
counterpart. It systematically injects **three noise types — random documents
(RD), random chat history (RC), and hard negatives (HN)** — across **11 datasets
in four families** (RAG, reasoning, alignment, tool use), and finds a
**catastrophic drop of up to ~80%** under contextual distractors (e.g., a
DeepSeek-R1-distilled 8B model degrading ~80.6% under hard negatives; Gemini-2.5-Pro
falling from 94.0% to 60.5% on one alignment task). Two findings are directly
load-bearing for our design: (1) an **inverse-scaling** effect — *more* test-time
reasoning makes things *worse* under hard negatives — and (2) **attention
visualizations showing models fixate on distractor tokens** on their wrong
answers. The authors also propose a Rationale-Aware Reward (RARE) that recovers
robustness, evidence that the failure is learnable signal-selection rather than
noise per se.

**Why it matters to us — and how we differ.** The HN-vs-RD result is the document
analogue of our **distractor *tier*** hypothesis: a same-package distractor (a
"hard negative" in code) should mislead more than a cross-cutting one. The
attention-fixation finding is the mechanism our per-tier `irrelevant_file_read_ratio`
tests *in code*, and the inverse-scaling result suggests we should sweep reasoning
effort as a secondary factor. But the noise here is *documents*, not source files
in a repository; there is no LOC scaling and no filesystem instrumentation.

[^loca]: The earlier spreadsheet recorded "accuracy halves from 8K to 256K" and
    "Claude-4.5-Opus best at short context." Re-reading the paper, the direction
    is right but the magnitude is larger than "halving" (Claude-4.5-Opus 96.0 →
    14.7, an ~81-point drop); the per-model figures above are taken from the paper
    text rather than the spreadsheet.

---

## 4. The task precedent: repository-level bug-fixing and localization

**SWE-bench** [6] established the genre: 2,294 real GitHub issues across 12 Python
repositories, each requiring coordinated edits across functions, classes, and
files, scored by hidden tests. At publication the best system (Claude 2) resolved
just **1.96%**; today, agent leaderboards exceed 70% on the curated *Verified*
subset — which is itself why *second-order* effects like bloat are now worth
isolating: the base task is no longer the bottleneck. SWE-bench gives us the
**hidden-test isolation philosophy** we adopt (design §4.4) and a weak prior for
baseline read-cost from its agent papers.

**Agentless** [7] is a useful counterpoint and a methodological gift. It shows a
deliberately *non*-agentic, three-phase pipeline — **localization → repair →
patch validation**, with no autonomous tool loop — reaches **32.00% on SWE-bench
Lite at ~$0.70/instance**, competitive with far more complex agents. More
important for us: its authors **manually audited** SWE-bench Lite, found issues
with leaked ground-truth patches or misleading descriptions, and released a
cleaned **Lite-S**. That audit is the direct precedent for our **seed-novelty
audit** — the requirement that neither an injected distractor nor the oracle patch
is secretly a restoration of upstream code.

**What this leaves open:** in both, repository size is *uncontrolled* and pass/fail
is the only first-class metric. Search cost (files/bytes read, tool calls before
first edit) is, at best, incidental tool-call data. We promote it to the primary
measurement.

---

## 5. The strongest code-domain signal: size hurts (observationally)

Two recent benchmarks show, in code, that scale degrades agents — but
*observationally*, by comparing different repositories.

**FeatBench** [8] evaluates feature implementation from **natural-language
requirements only** (no function signatures or code hints), with an automated,
*evolving* pipeline that rebuilds the benchmark from recent commits to resist
contamination (157 tasks across 27 actively-maintained repos). The headline:
even the best agent/LLM pair resolves only **29.94%**, and the dominant failure
mode is **"aggressive implementation" → scope creep and regressions** — agents
break working features by over-reaching. That failure taxonomy informs our own
failure classification (wrong-file edits, forbidden edits).[^feat]

**RepoMod-Bench** [9] is the cleanest size-effect curve in code. It benchmarks
repository *modernization* (cross-language translation) using an
**implementation-agnostic, hidden test suite** that checks functional equivalence
without exposing language-specific tests — 21 repos, 8 languages, 1.6M LOC,
11,616 tests, sizes from 14 to 211K LOC. Across four state-of-the-art agent
configurations it reports a **sharp scaling collapse: average pass rate falls
from 91.3% on projects under 10K LOC to 15.3% on projects over 50K LOC.** Its
hidden-equivalence-testing idea is one we can borrow to harden our verifiers.

**Why these matter — and the gap they leave.** They establish that the phenomenon
is real *in code* and give us magnitudes to calibrate our pre-registered
thresholds against (design §7.5). But because each compares *different
repositories with different tasks*, **repo size is confounded with task
difficulty** — they cannot say whether size *causes* the drop. Our controlled
design, holding the bug constant and scaling only irrelevant volume, is the causal
follow-on these papers invite.

[^feat]: The earlier spreadsheet recorded a "60–70% (small) → 10–30% (large)"
    resolved-rate split for FeatBench. That breakdown is not in the paper's
    abstract; only the 29.94% top resolved rate and the scope-creep finding are
    cited here. If the split appears in the paper body it can be added with a page
    reference.

---

## 6. Localization and retrieval: accuracy, not cost

A cluster of work treats *finding the right code* as the object of study — which
is half of our dependent variable. The consistent theme is that they measure
localization **accuracy**, never localization **cost**.

- **RepoBench** [10] and **CrossCodeEval** [11] showed that single-file
  benchmarks understate difficulty: realistic completion needs cross-file
  retrieval. They motivate localization as a core sub-problem but score
  completion quality and hold repository size fixed.
- **LocAgent** [12] represents a codebase as a **heterogeneous directed graph**
  (directory/file/class/function nodes; contain/import/invoke/inherit edges) with
  BM25 and hierarchical indexes, and gives the agent three tools
  (`SearchEntity`, `TraverseGraph`, `RetrieveEntity`). It introduces **Loc-Bench
  — 560 instances** deliberately balanced across bug reports (242), feature
  requests (150), performance (139), and security (29) issues, collected from
  GitHub issues *after* October 2024 to limit training-data leakage. It reports
  strong file-level Acc@5 (e.g., ~94% on SWE-bench-Lite with Claude-3.5; ~83% on
  Loc-Bench) and large cost savings from fine-tuned small models (~$0.05–0.09 vs.
  ~$0.66 per example).
- **Improving Code Localization with Repository Memory** [13] (the spreadsheet's
  "RepoMem") augments LocAgent with a **non-parametric memory built from commit
  history and linked issues**, plus functionality summaries of actively-evolving
  modules, and improves Accuracy@k on SWE-bench-Verified and SWE-bench-live.
- **CodeSearchNet** [14], **CoSQA** [15], and **CodeXGLUE** [16] ground semantic
  code retrieval and precision@k — the retrieval analogue of our
  `irrelevant_file_read_ratio`.

**The gap.** All of these ask *did the agent find the right file?* None asks *how
much did it read before finding it, and how much of that was irrelevant?* — and
none varies repository size as an independent variable. Our
`files_read_before_first_edit` / `bytes_read_before_first_edit` are absent from
the entire cluster. **Note:** the earlier spreadsheet merged LocAgent [12] and
Repository-Memory [13] into a single "RepoMem / LocAgent" row; they are two
distinct papers and are separated here.

---

## 7. Adjacent mechanisms: context overhead and iterative erosion

Two papers describe related ways agents degrade as repositories grow, via
different mechanisms than ours — useful Related-Work contrasts.

**Evaluating AGENTS.md** [17] (ETH Zurich, SRI Lab) is the closest *direct*
evidence that *more repository context can hurt coding agents*. Testing four
agent/model pairs (Claude Code + Sonnet-4.5; Codex + GPT-5.2 / GPT-5.1-mini; Qwen
Code + Qwen3-30b-coder) on SWE-bench Lite (no developer context files) and a new
**AGENTbench** of 138 instances that *do* carry developer-written context files,
it finds **LLM-generated context files slightly *reduce* success (−0.5% / −2% on
the two suites) while inflating cost by ~20–23%**, largely by inducing more
searching, reading, testing, and reasoning (14–22% more reasoning tokens).
Developer-written files help modestly (~+4%) at up to ~19% added cost. The
recommendation — context files should state *minimal* requirements — reinforces
the "more context = noise" intuition our work isolates. It studies *instruction*
files, not *file-count* growth, which is precisely our variable.

**SlopCodeBench** [18] (UW–Madison) measures degradation when agents iteratively
extend **their own** prior solutions: 36 problems, 196 checkpoints, 15 agents.
**No agent fully solves any problem end-to-end**; the best passes **14.8% of
checkpoints**; **structural erosion rises in 77% and verbosity in 75.5% of
trajectories**, and agent code is ~2.3× more verbose and ~2.0× more eroded than
human repositories. The mechanism is *self-authored* code-quality erosion, not
*injected* irrelevant files — a clean contrast that sharpens what our independent
variable is and isn't.[^slop]

[^slop]: The earlier spreadsheet recorded "93 checkpoints," "11 models," and
    "erosion in 80% of trajectories." The paper states 196 checkpoints, 15
    agents, and erosion/verbosity in 77% / 75.5% of trajectories; the verified
    figures are used here.

---

## 8. The white space we occupy

Laying the field on two axes — *is the noise variable controlled?* and *is it
source code in a repository?* — shows the empty cell.

| | Non-code domain | Source-code repository |
|---|---|---|
| **Controlled noise growth** | LOCA-bench, Lost in the Noise, NoLiMa | **← this benchmark (empty until now)** |
| **Observational / uncontrolled** | — | SWE-bench, FeatBench, RepoMod-Bench |

Three concrete, defensible contributions follow:

1. **A controlled repo-bloat experiment with irrelevant LOC as the sole
   independent variable.** No prior benchmark holds the target bug constant and
   scales *irrelevant* file volume (1×/5×/20×/50× by token budget). The controlled
   studies (LOCA-bench, Lost in the Noise) are non-code; the code studies
   (FeatBench, RepoMod-Bench) are observational.

2. **Localization *cost* as a first-class metric.** `files_read`, `bytes_read`,
   `search_calls`, and `input_tokens_*` split at the first-edit boundary, captured
   by dual filesystem + transcript instrumentation (design §6), are not the
   primary target of any prior coding-agent benchmark — the localization cluster
   (§6) measures *accuracy*, and SWE-bench-style papers report at most incidental
   tool-call counts.

3. **Distractor-tier analysis and a pre-registered practical-threshold verdict.**
   The same-package / same-layer / cross-cutting proximity taxonomy translates
   *Lost in the Noise*'s hard-negative finding into code, and the verdict criterion
   (≥2× cost rise, ≥0.20 irrelevant-read-ratio rise, ≥20 pp hidden-pass-rate drop —
   thresholds, not p-values) is methodologically novel for coding-agent benchmarks.

The per-study tactics that exploit these gaps — what to cite, adapt, reuse, or
position against — are developed in
[`integration-with-existing-studies.md`](integration-with-existing-studies.md).

---

## 9. References

The 17 arXiv entries verified against `export.arxiv.org/api/query`; the one
non-arXiv entry (NIAH [3]) verified via GitHub. Headline papers re-read from
full text. Verified 2026-06-12.

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
