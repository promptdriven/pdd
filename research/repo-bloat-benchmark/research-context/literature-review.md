# Literature Review — Do AI Coding Agents Get Worse as a Repository Fills with Irrelevant Code?

**Epic:** [#1429](https://github.com/promptdriven/pdd/issues/1429) (item 1 — Literature Review)
**Benchmark:** [`../design.md`](../design.md) · tracking issue [#1209](https://github.com/promptdriven/pdd/issues/1209)
**Background companion:** [`../agentic_cli_search.md`](../agentic_cli_search.md)

> **The question this project asks.** Give an AI coding agent the same bug, the
> same model, the same test that decides success, and the same starting code —
> then quietly grow the surrounding repository with more and more *plausible but
> irrelevant* files. What happens? We keep the actual task identical and measure
> three things as the repo grows: (1) how much work the agent does to find the
> right code before it makes its first edit, (2) how much of the irrelevant
> material actually ends up inside the model's working memory, and (3) whether the
> bug still gets fixed.

A note on plain language: this review is written to be read by people who are not
specialists in language-model evaluation. Three terms recur. A **coding agent** is
an AI system that can read files, run searches and commands, and edit code on its
own to complete a task. A model's **context window** is its working memory — the
text it can "see" at once; **tokens** are the units that fill it (roughly,
fragments of words). When we say an agent must **localize**, we mean it has to
find the right place in the code to change before it can fix anything.

## How to read this review

There are strong reasons to expect repository bloat to hurt AI coding agents — but
the evidence is **spread across three research communities that rarely cite one
another**:

- the **long-context** community asks: *does a model stay accurate when you fill
  its working memory?*
- the **distractor-robustness** community asks: *do irrelevant pieces of text
  mislead a model's reasoning?*
- the **coding-agent** community asks: *can an agent fix a real bug in a real
  codebase?*

No single paper sits where all three meet. This review walks the field from the
ideas *furthest* from our experiment to the ones *closest* to it — from the basic
motivation (§2), to the nearest methodological cousins (§3), to the
code-specific benchmarks (§4–§7) — and ends with the precise empty spot our
benchmark fills (§8).

**On sourcing.** An earlier version of this survey lived in a working
spreadsheet. Treating that as unverified, every one of the 18 works below was
re-checked at its original source: the **17 arXiv papers were checked against the
official arXiv record** (title, authors, date), and the one non-paper entry — the
**Needle-in-a-Haystack** retrieval test [3] — was checked against its GitHub
project. The headline papers were re-read so that every figure quoted here comes
from the paper itself, not from second-hand notes. That process caught a handful
of errors in the old spreadsheet; each correction is flagged in a footnote where
it occurs. The provenance summary lives in [`README.md`](README.md).

---

## 1. The verified source table

| # | Title | Authors | Date | Link | Status |
|---|----------------|---------|------|--------------|--------|
| 1 | NoLiMa: Long-Context Evaluation Beyond Literal Matching | Modarressi, Deilamsalehy, Dernoncourt, et al. | Feb 2025 | [2502.05167](https://arxiv.org/abs/2502.05167) | ✅ verified |
| 2 | LongBench: A Bilingual, Multitask Benchmark for Long Context Understanding | Bai et al. | Aug 2023 | [2308.14508](https://arxiv.org/abs/2308.14508) | ✅ verified |
| 3 | Needle-in-a-Haystack retrieval test (software) | G. Kamradt | 2023 | [GitHub](https://github.com/gkamradt/needle-in-a-haystack) | ✅ verified (software, not a paper) |
| 4 | LOCA-bench: Benchmarking Language Agents Under Controllable and Extreme Context Growth | Zeng, Huang, He | Feb 2026 | [2602.07962](https://arxiv.org/abs/2602.07962) | ✅ verified |
| 5 | Lost in the Noise: How Reasoning Models Fail with Contextual Distractors | Lee, Jo, Seo, Lee, Seo | Jan 2026 | [2601.07226](https://arxiv.org/abs/2601.07226) | ✅ verified |
| 6 | SWE-bench: Can Language Models Resolve Real-World GitHub Issues? | Jimenez, Yang, et al. | Oct 2023 | [2310.06770](https://arxiv.org/abs/2310.06770) | ✅ verified |
| 7 | Agentless: Demystifying LLM-based Software Engineering Agents | Xia, Deng, Dunn, Zhang | Jul 2024 | [2407.01489](https://arxiv.org/abs/2407.01489) | ✅ verified |
| 8 | FeatBench: Towards More Realistic Evaluation of Feature-level Code Generation | Chen, Li, Li | Sep 2025 (v2 Feb 2026) | [2509.22237](https://arxiv.org/abs/2509.22237) | ✅ verified |
| 9 | RepoMod-Bench: A Benchmark for Code Repository Modernization via Implementation-Agnostic Testing | Li, Ben-Israel, Raz, Ahmed, Serebro, Raux | Feb 2026 | [2602.22518](https://arxiv.org/abs/2602.22518) | ✅ verified |
| 10 | RepoBench: Benchmarking Repository-Level Code Auto-Completion Systems | Liu, Xu, McAuley | Jun 2023 | [2306.03091](https://arxiv.org/abs/2306.03091) | ✅ verified |
| 11 | CrossCodeEval: A Diverse and Multilingual Benchmark for Cross-File Code Completion | Ding et al. | Oct 2023 | [2310.11248](https://arxiv.org/abs/2310.11248) | ✅ verified |
| 12 | LocAgent: Graph-Guided LLM Agents for Code Localization | Chen et al. | Mar 2025 | [2503.09089](https://arxiv.org/abs/2503.09089) | ✅ verified — *introduces Loc-Bench* |
| 13 | Improving Code Localization with Repository Memory | Wang, Xu, Li, Gao, Xie, Sun, Chen | Oct 2025 | [2510.01003](https://arxiv.org/abs/2510.01003) | ✅ verified |
| 14 | CodeSearchNet Challenge: Evaluating the State of Semantic Code Search | Husain et al. | Sep 2019 | [1909.09436](https://arxiv.org/abs/1909.09436) | ✅ verified |
| 15 | CoSQA: 20,000+ Web Queries for Code Search and Question Answering | Huang et al. | May 2021 | [2105.13239](https://arxiv.org/abs/2105.13239) | ✅ verified |
| 16 | CodeXGLUE: A Machine Learning Benchmark Dataset for Code Understanding and Generation | Lu et al. | Feb 2021 | [2102.04664](https://arxiv.org/abs/2102.04664) | ✅ verified |
| 17 | Evaluating AGENTS.md: Are Repository-Level Context Files Helpful for Coding Agents? | Gloaguen et al. (ETH Zurich) | Feb 2026 | [2602.11988](https://arxiv.org/abs/2602.11988) | ✅ verified |
| 18 | SlopCodeBench: Benchmarking How Coding Agents Degrade Over Long-Horizon Iterative Tasks | Orlanski, Roy, Yun, et al. | Mar 2026 | [2603.24755](https://arxiv.org/abs/2603.24755) | ✅ verified |

*Author lists are shortened where long; the full lists are on each paper's page.
Every figure quoted below is taken from the papers' own text and tables.*

---

## 2. The motivation: accuracy fades inside the advertised window

The idea underneath this whole project is simple: a model's *usable* working
memory is smaller than its *advertised* working memory. Even when text fits well
inside a "128K-token" window, piling on more text makes the model less accurate.
Two results make this concrete.

**NoLiMa** [1] is the sharpest demonstration. The popular Needle-in-a-Haystack
test [3] — hide one fact ("the needle") in a long passage and ask the model to
retrieve it — turns out to be too easy, because the needle usually shares obvious
words with the question, so the model can latch onto the matching words instead of
truly understanding. NoLiMa removes that shortcut: it writes the hidden fact and
the question so they share *almost no words in common*, forcing the model to make
the connection by meaning rather than by word-matching. Tested on **13 models that
all claim to handle at least 128K tokens**, accuracy is near-perfect on short text
but falls steeply as the text grows — **by 32K tokens, 11 of the 13 score below
half of their own short-text accuracy**, and even GPT-4o, one of the strongest,
drops **from 99.3% to 69.7%**. **Why this matters to us:** a bloated repository is
exactly this kind of "no-obvious-match" haystack — the relevant code does not wave
a flag, and the agent has to reason past convincing look-alikes to find it. NoLiMa
is the cleanest evidence that the *size of the haystack itself*, not just the
difficulty of the task, is part of the problem. **LongBench** [2] provides the
broader long-context testing tradition that NoLiMa sharpens.

**What these leave open:** NoLiMa and LongBench work on ordinary prose, in a
single pass, with no agent, no source code, and no measurement of *what the model
did* to find the answer. They tell us bloat *should* hurt; they cannot tell us how
a coding agent's search-and-edit loop pays the price.

---

## 3. The closest cousins: turning a single "noise" dial

Two 2026 papers share the exact experimental move at the heart of our design —
**hold the task fixed and turn one noise dial up** — but in settings other than
code repositories. These are the works we must cite, and distinguish ourselves
from, most carefully.

### 3.1 LOCA-bench — controlled, almost-unlimited context growth for agents

**LOCA-bench** [4] (HKUST; project at `github.com/hkust-nlp/LOCA-bench`) is the
nearest methodological relative. Where NoLiMa grows a *fixed* block of text,
LOCA-bench grows the context an *agent* builds up as it works: it automatically
controls how much the agent's working memory fills, extending it "potentially to
infinity in a controlled way while keeping the underlying task the same." It tests
agents on tool-use tasks — a suite of 280 tools spanning email, calendar,
databases, spreadsheets, and e-commerce — using a standard reason-then-act agent
loop.

The decline is steep and steady. Growing the context across **8K → 16K → 32K →
64K → 96K → 128K → 256K tokens**, the paper reports (for example)
**Claude-4.5-Opus falling from 96.0% to 14.7%** and **GPT-5.2 (medium) from 72.0%
to 21.3%** over that range, with the **gap between frontier and open-source models
widening** as context grows (frontier models reach roughly 2–3× the accuracy of
open-source ones at 256K). Importantly, LOCA-bench also shows the drop is *partly
fixable by better engineering around the model*: housekeeping tricks — clearing
old tool results, summarizing, giving the agent an external memory, and especially
letting it call tools programmatically — recover a meaningful chunk of accuracy
(for instance, at 128K, GPT-5.2 climbs from 38.7% to 49.3%).

**Why it matters to us — and how we differ.** LOCA-bench validates the
"one-dial" design we adopt, *and* its recovery result is a useful warning: our
pilot must lock down how the agent manages its own context, or what looks like
"sensitivity to bloat" could really be a side effect of those housekeeping
choices. But LOCA-bench grows the context by feeding *tool and environment output*
into the conversation; it does **not** scatter *source-code* distractors through a
repository, does **not** watch which files the agent actually opens on disk, and
does **not** measure the cost paid *before the first edit*. The combination of a
software repository, file-level observation, and find-the-code cost is ours.[^loca]

### 3.2 Lost in the Noise — when convincing distractors mislead reasoning

**Lost in the Noise** [5] is the distractor-side counterpart (its benchmark is
named *NoisyBench*). It adds **three kinds of noise — random documents, random
chat history, and "hard negatives"** (distractors deliberately written to look
relevant) — across **11 datasets in four areas** (retrieval-augmented Q&A,
reasoning, alignment, and tool use). The effect is dramatic: convincing
distractors cause drops **as large as ~80%** (one 8-billion-parameter reasoning
model loses 80.6% of its accuracy under hard negatives; Gemini-2.5-Pro falls from
94.0% to 60.5% on one task). Two of its findings directly shape our design.
First, a **counterintuitive scaling effect**: giving a model *more* time to reason
makes it do *worse* when the distractors are convincing. Second, by visualizing
where the model "pays attention," the authors show it **fixates on the distractor
text** precisely on the questions it gets wrong. They also show the failure can be
trained away with a better reward signal — evidence that the problem is *which
information the model chooses to trust*, not noise as such.

**Why it matters to us — and how we differ.** The hard-negative result is the
prose version of our **"how close is the distractor" hypothesis**: in code, a
distractor file from the *same package* as the bug should mislead more than one
from a distant corner of the project. The attention-fixation finding is the
mechanism our experiment looks for *in code*, and the counterintuitive
reasoning result suggests we should also vary how hard the agent is told to think.
But here the noise is *documents*, not source files in a real project; there is no
growing codebase and no observation of what the agent reads off disk.

[^loca]: The earlier spreadsheet summarized LOCA-bench as "accuracy halves from 8K
    to 256K" and "Claude-4.5-Opus best at short context." Re-reading the paper, the
    direction is right but the drop is far larger than "halving" (Claude-4.5-Opus
    96.0% → 14.7%, an ~81-point fall); the per-model figures above come from the
    paper itself.

---

## 4. The task itself: fixing real bugs in real repositories

**SWE-bench** [6] created the genre: 2,294 real GitHub issues across 12 Python
projects, each needing coordinated edits across functions, classes, and files, and
each graded by a hidden test. When it was published, the best system (Claude 2)
fixed just **1.96%** of the issues; today the top agents clear well over 70% on
the curated *Verified* subset. That progress is exactly *why* second-order effects
like bloat are now worth isolating — the basic task is no longer the bottleneck.
SWE-bench also gives us the **hidden-test idea** we adopt (design §4.4): success is
decided by a test the agent never sees, so it cannot game its way to a pass.

**Agentless** [7] is a useful counterpoint and a methodological gift. It shows
that a deliberately *non*-agentic, three-step pipeline — **find the code → fix it →
check the patch**, with no autonomous tool loop — reaches **32.00% on SWE-bench
Lite at about $0.70 per issue**, competitive with far more elaborate agents. More
useful for us: its authors **hand-audited** SWE-bench Lite, found cases where the
answer had leaked into the issue text or the description was misleading, and
released a cleaned-up version (**Lite-S**). That audit is the direct precedent for
our own **answer-novelty check** — making sure that neither an added distractor nor
the intended fix is secretly a copy of the project's real upstream code.

**What these leave open:** in both, the size of the repository is *uncontrolled*,
and pass-or-fail is the only headline number. The *cost of searching* — how many
files and how much text the agent reads before its first edit — is, at best,
incidental. We promote that cost to the main measurement.

---

## 5. The clearest code signal: bigger hurts (but only by comparison)

Two recent benchmarks show, in code, that scale degrades agents — but they show it
*by comparing different repositories*, not by controlling size directly.

**FeatBench** [8] asks agents to implement a feature from a **plain-English
description only** (no function signatures, no code hints), using an automatically
*refreshing* pipeline that rebuilds the benchmark from recent commits so models
cannot have memorized the answers (157 tasks across 27 actively maintained
projects). The headline: even the best agent-and-model pairing succeeds only
**29.94%** of the time, and the most common failure is **over-reaching** — the
agent does too much, creeps beyond the request, and breaks features that already
worked. That failure pattern informs how we categorize our own failures (editing
the wrong file, editing files it should not touch).

**RepoMod-Bench** [9] is the cleanest size-versus-success curve in code. It
benchmarks **modernizing** a project (translating it to another language) and
judges success with a hidden test suite that checks whether the new code *behaves*
the same, without revealing language-specific tests — 21 projects, 8 languages,
1.6M lines, 11,616 tests, ranging from 14 to 211,000 lines. Across four
state-of-the-art agent setups it reports a **sharp collapse: average success falls
from 91.3% on projects under 10,000 lines to 15.3% on projects over 50,000
lines.** Its "judge by behavior, not by matching tests" idea is one we can borrow
to make our own hidden tests harder to game.

**Why these matter — and the gap they leave.** They establish that the effect is
real *in code*, and they give us magnitudes to calibrate our pre-set thresholds
against (design §7.5). But because each one compares *different projects with
different tasks*, **size is tangled up with difficulty** — they cannot say whether
size itself *causes* the drop. Our controlled design — hold the bug fixed and
scale only the irrelevant volume — is exactly the cause-and-effect follow-up these
papers invite.[^feat]

[^feat]: The earlier spreadsheet recorded a "60–70% (small) → 10–30% (large)"
    split for FeatBench. That breakdown is not in the paper's abstract; only the
    29.94% top success rate and the over-reaching failure mode are cited here. If
    the split appears in the paper body it can be added with a page reference.

---

## 6. Finding the code: prior work measures *accuracy*, never *cost*

A cluster of work studies *finding the right code* as a problem in its own right —
which is half of what we measure. The consistent theme: they all score how *often*
the agent finds the right place, never how much *effort* it spent getting there.

- **RepoBench** [10] and **CrossCodeEval** [11] showed that single-file tests
  understate the difficulty: realistic code completion needs information pulled
  from *other* files. They establish "find the relevant code across files" as a
  core sub-problem, but they grade the quality of the completion and keep the
  repository size fixed.
- **LocAgent** [12] turns a codebase into a **graph** — folders, files, classes,
  and functions as nodes, with their import, call, and inheritance links as
  edges — paired with classic keyword search, and gives the agent three tools to
  explore it. It also introduces **Loc-Bench**, a 560-issue test set deliberately
  balanced across bug reports (242), feature requests (150), performance (139),
  and security (29), drawn from GitHub issues filed *after* October 2024 to avoid
  overlap with training data. It reports strong "is the right file in the agent's
  top 5 guesses" rates — about 94% on SWE-bench-Lite and about 86% on its own
  Loc-Bench (with Claude-3.5)[^loc] — and large cost savings from small fine-tuned
  models (~$0.05–0.09 versus ~$0.66 per example).
- **Improving Code Localization with Repository Memory** [13] adds to LocAgent an
  **external memory built from a project's commit history and linked issues**,
  plus short summaries of the parts of the codebase that change most often, and
  improves find-the-file accuracy on two SWE-bench variants.
- **CodeSearchNet** [14], **CoSQA** [15], and **CodeXGLUE** [16] established
  semantic code search — matching a natural-language query to the right code — and
  the accuracy measures that go with it. They are the search-quality ancestor of
  the "how much of what the agent read was irrelevant?" question we ask.

**The gap.** Every one of these asks *did the agent find the right file?* None
asks *how much did it read before finding it, and how much of that was wasted?* —
and none varies repository size as the thing under study. The
read-before-you-edit cost we put front and center is absent from this entire
cluster.[^merge]

[^loc]: An earlier draft listed the Loc-Bench figure as "~83%." The paper's actual
    LocAgent result with Claude-3.5 is ~86% (86.07% on the top-5 measure); the
    SWE-bench-Lite figure (~94%) was already correct. Corrected here.

[^merge]: The earlier spreadsheet merged LocAgent [12] and Repository-Memory [13]
    into one row. They are two distinct papers (different teams, different
    contributions) and are separated here.

---

## 7. Two related ways agents degrade — by different routes than ours

Two more papers describe agents getting worse as repositories grow, but through
*different mechanisms* than the one we study — useful contrasts for a
related-work section.

**Evaluating AGENTS.md** [17] (ETH Zurich) is the closest *direct* evidence that
*more repository context can hurt a coding agent*. Testing four agent-and-model
pairings on SWE-bench Lite (no project context files) and a new 138-issue set that
*does* include them, it finds that **AI-generated context files slightly *lower*
success (−0.5% and −2% on the two suites) while raising cost by about 20–23%** —
mostly by prompting the agent to search, read, test, and reason more (14–22% more
reasoning tokens). Human-written context files help only modestly (about +4%) at
up to ~19% more cost. The takeaway — context files should say only the *minimum*
necessary — reinforces the "more context can become noise" intuition our work
isolates. It studies *instruction* files, though, not a growing *count of code
files*, which is precisely our variable.

**SlopCodeBench** [18] (University of Wisconsin–Madison) measures what happens when
agents repeatedly extend **their own** earlier work: 36 problems, 196 checkpoints,
15 agents. **No agent fully finishes a single problem**; the best clears only
**14.8% of checkpoints**; quality erodes in **77%** of runs and code grows
needlessly verbose in **75.5%**, leaving agent code roughly 2.3× more verbose and
2.0× more tangled than comparable human-written projects. The mechanism here is
*self-inflicted* quality decay over many turns — a clean contrast that sharpens
what our variable *is* (irrelevant files injected from outside) and *is not*.[^slop]

[^slop]: The earlier spreadsheet recorded "93 checkpoints," "11 models," and
    "erosion in 80% of trajectories." The paper states 196 checkpoints, 15 agents,
    and erosion/verbosity in 77% / 75.5% of runs; the verified figures are used
    here.

---

## 8. The empty spot we fill

Lay the field on two axes — *is the amount of noise actually controlled?* and *is
the noise source code in a real repository?* — and one cell is empty:

| | Noise is ordinary text | Noise is source code in a repo |
|---|---|---|
| **Amount of noise is controlled** | LOCA-bench, Lost in the Noise, NoLiMa | **← this benchmark (empty until now)** |
| **Amount is uncontrolled (observed)** | — | SWE-bench, FeatBench, RepoMod-Bench |

Three concrete, defensible contributions follow:

1. **A controlled bloat experiment with irrelevant code as the only thing that
   changes.** No prior benchmark holds the target bug fixed and scales *irrelevant*
   file volume (1× / 5× / 20× / 50×, measured in tokens). The controlled studies
   (LOCA-bench, Lost in the Noise) are not about code; the code studies (FeatBench,
   RepoMod-Bench) only observe size differences rather than control them.

2. **The cost of finding the code, treated as a primary result.** How many files
   and how much text the agent reads, how many searches it runs, and how many
   tokens it spends — all split at the moment of the first edit — are not the main
   target of any prior coding-agent benchmark. The find-the-code cluster (§6)
   measures *accuracy*; SWE-bench-style work reports search effort only in passing.

3. **A "how close is the distractor" analysis and a verdict decided in advance.**
   Sorting distractors by how near they sit to the bug (same package / same layer /
   distant) carries the *Lost in the Noise* hard-negative finding into code, and
   the success criteria — set *before* any model runs, as common-sense cutoffs
   rather than statistical significance tests (at least a 2× rise in cost, at least
   a 0.20 rise in the share of reads that are irrelevant, at least a 20-point drop
   in fix rate) — are themselves a methodological novelty for this kind of
   benchmark.

How we plan to use each study — what to cite, adapt, reuse, or position against —
is worked out in
[`integration-with-existing-studies.md`](integration-with-existing-studies.md).

---

## 9. References

All 17 arXiv entries were checked against the official arXiv record; the one
non-paper entry (the Needle-in-a-Haystack test [3]) was checked on GitHub. Headline
papers were re-read in full. Last verified 2026-06-17.

1. Modarressi et al. *NoLiMa: Long-Context Evaluation Beyond Literal Matching.* arXiv:2502.05167.
2. Bai et al. *LongBench: A Bilingual, Multitask Benchmark for Long Context Understanding.* arXiv:2308.14508.
3. Kamradt. *Needle-in-a-Haystack (LLMTest_NeedleInAHaystack).* https://github.com/gkamradt/needle-in-a-haystack.
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
