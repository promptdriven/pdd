# Video References & Sources

Research sources for claims made in the 3Blue1Brown-style PDD video.

---

## Economics of Darning / Sock History

### When Darning Became Obsolete (mid-1960s)

- **Philadelphia Tribune** — "Back In The Day: Darning socks used to pay off"
  https://www.phillytrib.com/commentary/backintheday/back-in-the-day-darning-socks-used-to-pay-off/article_51115cbd-ab34-5859-bbcc-ce9be9cd4839.html
  *Key claim: The Great Depression generation was the last to routinely darn; Boomer children largely abandoned the practice.*

- **Vintage Dancer** — "Vintage Men's Socks History: 1900 to 1960s"
  https://vintagedancer.com/vintage/history-vintage-mens-socks/
  *Key claim: Synthetic fibers (nylon, polyester, spandex) replaced wool through the 1950s-60s, making socks cheaper and more durable.*

- **Science History Institute** — "Nylon: A Revolution in Textiles"
  https://www.sciencehistory.org/stories/magazine/nylon-a-revolution-in-textiles/
  *Key claim: Nylon invented 1935, debuted in stockings 1939, redirected to military 1942-45, mass consumer adoption postwar.*

- **Smithsonian Magazine** — "Stocking Series: Wartime Rationing and Nylon Riots"
  https://www.smithsonianmag.com/arts-culture/stocking-series-part-1-wartime-rationing-and-nylon-riots-25391066/
  *Key claim: 40,000 people lined up in Pittsburgh in 1946 for 13,000 pairs of nylon stockings.*

- **Wikipedia** — "Throw-away society"
  https://en.wikipedia.org/wiki/Throw-away_society
  *Key claim: Life magazine coined "Throwaway Living" in August 1955.*

### 1950 Sock Prices & Wages

- **Poppy's Vintage Clothing** — 1950s Tootal wool socks with original $1.00 price tag
  https://www.poppysvintageclothing.com/products/vintage-1950s-mens-tootal-wool-socks-maroon-size-l-11-unused-with-original-bill
  *Key claim: Quality wool socks cost ~$1.00 per pair in the 1950s.*

- **FRED (St. Louis Fed)** — Average Hourly Earnings, Manufacturing (CES3000000008)
  https://fred.stlouisfed.org/series/CES3000000008
  *Key data: Manufacturing wages ~$1.44/hr (1950), ~$1.86/hr (1955), ~$2.26/hr (1960).*

- **FRED (St. Louis Fed)** — Consumer Price Index: Apparel (CPIAPPSL)
  https://fred.stlouisfed.org/series/CPIAPPSL
  *Key data: Apparel CPI rose only ~13% from 1950 to 1960, while wages rose ~57%. Cost of socks in labor-hours fell sharply.*

- **University of Missouri Library** — Prices and Wages by Decade: 1950-1959
  https://libraryguides.missouri.edu/pricesandwages/1950-1959
  *Key data: Average hours and earnings for production workers in manufacturing, 1919-1960.*

- **BLS** — "One Hundred Years of Price Change"
  https://www.bls.gov/opub/mlr/2014/article/one-hundred-years-of-price-change-the-consumer-price-index-and-the-american-inflation-experience.htm
  *Key claim: Early-to-mid 1950s were "probably as close as the United States has come to price stability."*

---

## AI Milestone Dates (Used in Video Chart)

| Model | Date | Source |
|-------|------|--------|
| Codex / GitHub Copilot | Aug 2021 (Codex) / Jun 2021 (Copilot preview) | [Wikipedia: OpenAI Codex](https://en.wikipedia.org/wiki/OpenAI_Codex), [Wikipedia: GitHub Copilot](https://en.wikipedia.org/wiki/GitHub_Copilot) |
| GPT-4 | March 14, 2023 | [Times of AI: GPT Version Timeline](https://www.timesofai.com/industry-insights/gpt-version-timeline/) |
| Claude 3.5 Sonnet | June 20, 2024 | [Anthropic: Introducing Claude 3.5 Sonnet](https://www.anthropic.com/news/claude-3-5-sonnet) |
| Claude 3.7 Sonnet | February 2025 | [Anthropic: Claude 3.7 Sonnet and Claude Code](https://www.anthropic.com/news/claude-3-7-sonnet) |
| Frontier cluster (Opus 4.5, GPT 5.2, Gemini 3) | Late 2025 | [LMArena Leaderboard](https://lmarena.ai/leaderboard/) |

### Models Removed from Chart (with rationale)

| Model | Date | Why removed |
|-------|------|-------------|
| GPT-3 | June 2020 | No meaningful coding impact. ["Not useful for programmers other than as an experiment."](https://towardsdatascience.com/gpt-3-or-any-ai-wont-kill-coding-f4cabd3a536b/) |
| Claude 1.0 | March 2023 | Limited release, not known for coding. [Coding dominance came with 3.5 Sonnet in 2024.](https://www.anthropic.com/news/claude-3-5-sonnet) |
| Gemini 1.0 | December 2023 | Initial release had modest coding impact. Significant capability came later with 1.5 Pro. |

---

## AI Coding Benchmark Progression

### SWE-bench (Real-World Bug Fixing — Gold Standard)

| Period | Top Score | Key Model(s) | Source |
|--------|----------|--------------|--------|
| Oct 2023 | ~4% | GPT-3.5, Claude 2 | [SWE-bench Leaderboards](https://www.swebench.com/) |
| Apr 2024 | ~12-18% | SWE-agent + GPT-4 | [SWE-bench Leaderboards](https://www.swebench.com/) |
| Jun-Jul 2024 | ~38-49% | Claude 3.5 Sonnet | [Anthropic: SWE-bench Performance](https://www.anthropic.com/research/swe-bench-sonnet) |
| Late 2024 | ~49-65% | Claude 3.5 Sonnet v2, o1 | [Anthropic: 3.5 Models Update](https://www.anthropic.com/news/3-5-models-and-computer-use) |
| Feb 2025 | ~70.3% | Claude 3.7 Sonnet | [Anthropic: Claude 3.7 Sonnet](https://www.anthropic.com/news/claude-3-7-sonnet) |
| Late 2025 | ~77-81% | Claude Opus 4.5, GPT 5.2, Gemini 3 | [SWE-bench Verified Leaderboard](https://llm-stats.com/benchmarks/swe-bench-verified) |

- **Stanford AI Index 2025**: "AI systems could solve just 4.4% of coding problems in 2023—a figure that jumped to 71.7% in 2024."
  https://hai.stanford.edu/ai-index/2025-ai-index-report/technical-performance

### HumanEval (Function-Level Coding)

| Model | Score | Source |
|-------|-------|--------|
| Codex (2021) | ~27-37% | [OpenAI Codex Paper](https://arxiv.org/abs/2107.03374) |
| GPT-4 (2023) | ~80% | [OpenAI GPT-4 Technical Report](https://arxiv.org/abs/2303.08774) |
| GPT-4o (2024) | 90.2% | [Qodo: Comparison of Coding Models](https://www.qodo.ai/blog/comparison-of-claude-sonnet-3-5-gpt-4o-o1-and-gemini-1-5-pro-for-coding/) |
| Claude 3.5 Sonnet (2024) | 92% | [Anthropic: Claude 3.5 Sonnet](https://www.anthropic.com/news/claude-3-5-sonnet) |

### Chatbot Arena Coding Elo Rankings

- **May 2023**: GPT-4 leads at Elo 1274, ~200 points above best open-source model.
  https://lmsys.org/blog/2023-05-25-leaderboard/

- **March 2024**: Claude 3 Opus overtakes GPT-4 — first time GPT-4 dethroned since May 2023.
  https://decrypt.co/223787/anthropic-claude-ai-versus-openai-chatgpt-llm-arena-ranking

- **June 2024**: Claude 3.5 Sonnet debuts, ties for #1 in coding Arena.
  https://www.anthropic.com/news/claude-3-5-sonnet

- **Late 2024**: Claude 3.5 Sonnet (Oct edition) tops coding leaderboard.
  https://www.anthropic.com/news/3-5-models-and-computer-use

- **Late 2025**: Claude Opus 4.5 holds 1542 Elo (all-time high), Anthropic holds 7 of top 11 coding spots.
  https://lmarena.ai/leaderboard/

### Early Copilot Limitations (Autocomplete Era)

- **The New Stack** — "GitHub Copilot: A Powerful, Controversial Autocomplete for Developers"
  https://thenewstack.io/github-copilot-a-powerful-controversial-autocomplete-for-developers/
  *Key claim: Analysts described Copilot as "more the next generation of autocomplete." Accurate ~43% on first try.*

- **Towards Data Science** — "GPT-3 (or Any AI) Won't Kill Coding"
  https://towardsdatascience.com/gpt-3-or-any-ai-wont-kill-coding-f4cabd3a536b/
  *Key claim: GPT-3 was "not that useful right now for programmers other than as an experiment."*

---

## AI Productivity: Individual Speedup vs. Total Throughput

### Individual Task Speedup: 55% (with important caveats)

- **GitHub Blog** — "Research: Quantifying GitHub Copilot's Impact on Developer Productivity and Happiness" (2022)
  https://github.blog/news-insights/research/research-quantifying-github-copilots-impact-on-developer-productivity-and-happiness/
  *Key finding: Developers completed tasks 55% faster with Copilot (P=.0017, 95% CI: 21-89%). Task: implement an HTTP server in JavaScript.*

- **arXiv** — "The Impact of AI on Developer Productivity: Evidence from GitHub Copilot" (Peng et al., 2023)
  https://arxiv.org/abs/2302.06590
  *Key finding: Treatment group completed task 55.8% faster. Less experienced programmers benefited more.*
  **Methodology limitations (cited in script):** Only 95 participants (45 treated, 50 control). Single greenfield task (HTTP server in JavaScript). Participants mostly 25-34 years old, primarily from India and Pakistan, ~6 years experience. Results reflect best-case scenario for AI tools: small, self-contained, greenfield work.

### Overall Throughput: No Significant Change

- **Uplevel Data Labs** — "Can Generative AI Improve Developer Productivity?" (2024)
  https://uplevelteam.com/blog/ai-for-developer-productivity
  https://resources.uplevelteam.com/gen-ai-for-coding
  *Key finding: 785 developers (351 Copilot, 434 control), enterprise customers, Jan 2023–Apr 2024. PR cycle time decreased by only 1.7 minutes (negligible). Bug rate increased 41% in Copilot group. Uplevel PM quote: "People are ending up being more reviewers for this code than in the past, and you might have some false faith that the code is doing what you expect."*

- **Visual Studio Magazine** — "Another Report Weighs In on GitHub Copilot Dev Productivity" (Uplevel coverage, 2024)
  https://visualstudiomagazine.com/articles/2024/09/17/another-report-weighs-in-on-github-copilot-dev-productivity.aspx

- **DevOps.com** — "Study Finds No DevOps Productivity Gains from Generative AI" (Uplevel coverage, 2024)
  https://devops.com/study-finds-no-devops-productivity-gains-from-generative-ai/

- **METR** — "Measuring the Impact of Early-2025 AI on Experienced Open-Source Developer Productivity" (2025)
  https://metr.org/blog/2025-07-10-early-2025-ai-experienced-os-dev-study/
  *Key finding: Randomized controlled trial. 16 experienced developers on repos averaging 22k+ stars and 1M+ lines. AI actually increased completion time by 19%. Developers predicted AI would save 24%; after completing tasks they still believed it saved 20%. Actual result: 19% slower. The 39-point perception gap (believed +20%, actual -19%) is cited in the script.*

- **arXiv** — "Measuring the Impact of Early-2025 AI on Experienced Open-Source Developer Productivity"
  https://arxiv.org/abs/2507.09089
  *Key details: 246 tasks, 140+ hours of screen recordings. Developers accepted <44% of AI suggestions. 75% reported reading every line of AI output. 56% made major modifications to clean up AI code.*

- **Sean Goedecke** — "METR's AI productivity study is really good" (Analysis)
  https://www.seangoedecke.com/impact-of-ai-study/

### Code Quality Degradation

- **GitClear** — "AI Copilot Code Quality: 2025 Data Suggests 4x Growth in Code Clones" (2025)
  https://www.gitclear.com/ai_assistant_code_quality_2025_research
  *Key findings (cited in script): 211 million lines of code analyzed across 2020-2024. Code cloning up 4x—copy/paste lines rose from 8.3% to 12.3%. Refactoring collapsed—"moved" (refactored) lines dropped from 24.1% to 9.5% (60% decline). Code churn up 44%—7.9% of new code revised within 2 weeks vs 5.5% in 2020.*

- **CodeRabbit** — "State of AI vs Human Code Generation" (2025)
  https://www.coderabbit.ai/blog/state-of-ai-vs-human-code-generation-report
  *Key findings (cited in script): 470 PRs analyzed (320 AI-co-authored, 150 human-only). AI-generated PRs: 10.83 issues each vs 6.45 for human PRs (1.7× more). Logic errors up 75%. Performance issues up ~8×. Security vulnerabilities up 1.5-2×.*

- **BusinessWire** — "CodeRabbit Report Finds AI-Written Code Produces ~1.7x More Issues" (press release)
  https://www.businesswire.com/news/home/20251217666881/en/

- **The Register** — "AI-authored code needs more attention, contains worse bugs" (CodeRabbit coverage)
  https://www.theregister.com/2025/12/17/ai_code_bugs/

- **Stack Overflow** — 2025 Developer Survey: AI Section
  https://survey.stackoverflow.co/2025/ai
  *Key finding: Only 52% of developers agree AI tools have had a positive effect on productivity. Sentiment dropped to 60%, down from 70%+ in 2023-2024.*

### Enterprise Field Studies (More Moderate Gains)

- **MIT / Microsoft & Accenture** — "The Productivity Effects of Generative AI: Evidence from a Field Experiment with GitHub Copilot"
  https://mit-genai.pubpub.org/pub/v5iixksv
  *Key finding: 4,867 developers across Microsoft, Accenture, and a Fortune 100 company. 26% more PRs/week overall (13-22% at Microsoft, 8-9% at Accenture). Does not account for quality/debt tradeoffs.*

- **Google Internal RCT** — "How much does AI impact development speed? An enterprise-based randomized controlled trial" (2024)
  https://arxiv.org/abs/2410.12944
  *Key finding: 96 Google engineers. AI-assisted group completed tasks 21% faster (96 min vs 114 min). More senior developers and those who code more hours per day benefited most. Confidence interval is large.*

---

## Software Maintenance Costs (80-90%)

- **Wikipedia** — "Software maintenance"
  https://en.wikipedia.org/wiki/Software_maintenance
  *Key claim: Maintenance is the last and typically longest phase of the software lifecycle, comprising 80-90% of lifecycle cost.*

- **ResearchGate** — "Development of Software maintenance costs as percentage of total cost"
  https://www.researchgate.net/figure/Development-of-Software-maintenance-costs-as-percentage-of-total-cost-Floris-and-Harald_fig2_236189469
  *Key claim: About 90% of software life cost is related to its maintenance phase.*

- **PMC/NIH** — "Which Factors Affect Software Projects Maintenance Cost More?"
  https://pmc.ncbi.nlm.nih.gov/articles/PMC3610582/
  *Key claim: Contribution is higher than 90% of total costs. A few decades ago, this figure stood at 50%.*

- **Vention** — "Software Maintenance Costs: 2024 Benchmark Overview"
  https://ventionteams.com/enterprise/software-maintenance-costs
  *Key claim: 50-80% range commonly cited. IBM research indicates 50-75%, Gartner estimates 55-80%.*

---

## Codebase Size, Complexity & AI Context Limitations

### Maintenance Cost Scaling (Exponential with Size)

- **Banker, Datar, Kemerer & Zweig** — "Software Complexity and Maintenance Costs" (Communications of the ACM, 1993)
  https://dl.acm.org/doi/10.1145/163359.163375
  *Key finding: Maintenance costs scale exponentially—not linearly—with codebase size. Doubling the codebase more than doubles the maintenance burden.*

### Optimal Module Size (The Goldilocks Conjecture)

- **Hatton** — "Reexamining the Fault Density–Component Size Connection" (IEEE Software, 1997)
  https://ieeexplore.ieee.org/document/585176
  *Key finding: Modules of 200-400 lines of code have the lowest defect density. Smaller modules have too much interface overhead; larger modules become too complex to maintain. This is the "Goldilocks zone" for module size—and matches the size generated by a focused prompt.*

### Context Window Degradation (Context Rot)

- **Hong et al. / Chroma** — "Context Rot: How Increasing Input Tokens Impacts LLM Performance" (2025)
  https://research.trychroma.com/context-rot
  https://github.com/chroma-core/context-rot
  *Key finding (cited in script): Evaluated 18 SOTA models including GPT-4.1, Claude 4, Gemini 2.5, Qwen3. Performance degrades non-uniformly as context grows. Degradation worsens as needle-question similarity decreases—reflecting realistic scenarios where exact matches are rare. Different model families degrade differently (GPT series: erratic; others: more predictable).*

- **arXiv / EMNLP 2025** — "Context Length Alone Hurts LLM Performance Despite Perfect Retrieval" (2025)
  https://arxiv.org/abs/2510.05381
  https://aclanthology.org/2025.findings-emnlp.1264.pdf
  *Key finding (cited in script): Even when models perfectly retrieve all relevant information, performance degrades 13.9%–85% as input length increases. Degradation occurs even when irrelevant tokens are replaced with whitespace, and even when models are forced to attend only to relevant tokens. Sheer input length alone hurts reasoning, independent of retrieval quality.*

- **Liu et al.** — "Lost in the Middle: How Language Models Use Long Contexts" (TACL 2024)
  https://arxiv.org/abs/2307.03172
  https://direct.mit.edu/tacl/article/doi/10.1162/tacl_a_00638/119630/
  *Key finding: Performance degrades by more than 30% when relevant information shifts from start/end to middle of context. Models perform best on information at beginning and end, worst in the middle.*

### Agentic Tool Retrieval Benchmarks

- **Jolt AI** — "Benchmarking Large Codebase Search with Cursor, Windsurf, Claude Code, Copilot, Codex, Augment, and Jolt" (2025)
  https://www.usejolt.ai/blog/large-codebase-search-benchmark
  *Key finding (cited in script): Tested on real PRs from Django, Grafana, Kubernetes. Pure vector search (GitHub Copilot): sub-minute but fails to find the right files. Agentic search (Codex, Claude Code): finds more relevant code but takes 3-5 minutes per search. Claude Code's search quality was "significantly worse"—missed important files or suggested irrelevant ones. 50+ searches per complex PR means ~3 hours of search time for Claude Code.*

- **OfficeChai** — "Claude Researcher Explains How Agentic Search Performed Better Than RAG" (Boris Cherny interview)
  https://officechai.com/ai/claude-researcher-explains-how-agentic-search-performed-better-than-rag-for-code-generation/
  *Key context: Boris Cherny (Claude Code lead engineer) confirmed they chose agentic grep over RAG. Initial metric was "vibes"—"it just felt better." Architecture chose minimalism: no servers, no indexes, just CLI.*

- **Milvus Blog** — "Why I'm Against Claude Code's Grep-Only Retrieval" (2025)
  https://milvus.io/blog/why-im-against-claude-codes-grep-only-retrieval-it-just-burns-too-many-tokens.md
  *Key criticism: Grep-based approach burns excessive tokens and fails on conceptual queries like "Where do we handle authentication?" that require semantic understanding.*

- **Factory.ai** — "The Context Window Problem: Scaling Agents Beyond Token Limits" (2025)
  https://factory.ai/news/context-window-problem
  *Key finding: Enterprise monorepo spans millions of tokens; even largest context windows hold ~1M. Token pricing makes "just stuff more code" strategies untenable. Factory's solution: repository overviews, semantic search, targeted file operations.*

---

## DORA Report: AI as Amplifier (2025)

- **Google DORA** — "State of AI-assisted Software Development 2025"
  https://dora.dev/research/2025/dora-report/
  *Key finding (cited in script): AI acts as an amplifier—magnifies existing organizational strengths and weaknesses. AI coding assistants boost individual output (21% more tasks, 98% more PRs merged) but organizational delivery metrics stay flat. AI adoption continues to have a negative relationship with software delivery stability. Critical success factors: strong automated testing and small batches.*

- **InfoQ** — "DORA Report Finds AI Is an Amplifier in Software Development, But Trust Remains Low" (2025)
  https://www.infoq.com/news/2025/09/dora-state-of-ai-in-dev-2025/

- **Google Cloud Blog** — "Announcing the 2025 DORA Report"
  https://cloud.google.com/blog/products/ai-machine-learning/announcing-the-2025-dora-report

---

## Technical Debt: Compound Costs

- **McKinsey Digital** — "Breaking technical debt's vicious cycle to modernize your business" (2024)
  https://www.mckinsey.com/capabilities/mckinsey-digital/our-insights/breaking-technical-debts-vicious-cycle-to-modernize-your-business
  *Key finding (cited in script): Organizations with high tech debt spend 40% more on maintenance and deliver features 25-50% slower. Tech debt accounts for ~40% of IT balance sheets.*

- **Stripe** — "The Developer Coefficient" (2018)
  https://stripe.com/files/reports/the-developer-coefficient.pdf
  https://stripe.com/newsroom/stories/developer-coefficient
  *Key finding (cited in script): Developers spend 42% of their time dealing with technical debt and bad code—approximately 13.5 hours/week on technical debt and 3.8 hours/week on bad code. Script rounds to "a third" for technical debt specifically. $85 billion in annual opportunity cost.*

- **CISQ** — "The Cost of Poor Software Quality in the US: A 2022 Report"
  https://www.it-cisq.org/the-cost-of-poor-quality-software-in-the-us-a-2022-report/
  https://www.it-cisq.org/wp-content/uploads/sites/6/2022/11/CPSQ-Report-Nov-22-2.pdf
  *Key finding (cited in script): Accumulated technical debt in the US reached $1.52 trillion (up from $1.31T in 2020). Total cost of poor software quality: $2.41 trillion. Technical debt is the largest obstacle to making changes in existing codebases.*

- **SIG** — Empirical model of technical debt and interest (ACM 2011)
  https://dl.acm.org/doi/abs/10.1145/1985362.1985364
  *Key finding: Debt follows compound interest formula: Technical Debt Growth = Initial Debt × (1 + Interest Rate)^Time. Based on empirical data of 44 systems.*

---

## Natural Language Efficiency for LLM Code Generation

- **MIT CSAIL** — "Natural language boosts LLM performance in coding, planning, and robotics" (ICLR 2024)
  https://news.mit.edu/2024/natural-language-boosts-llm-performance-coding-planning-robotics-0501
  *Key finding (cited in script): Three neurosymbolic frameworks (LILO, Ada, LGA) showed natural language context dramatically improves LLM task performance. Ada + GPT-4 improved task accuracy by 59% (kitchen simulator) and 89% (Mini Minecraft) vs code-only baseline. NL encodes background knowledge and abstractions that pure code doesn't.*

- **ACL 2024 Findings** — "Code Needs Comments: Enhancing Code LLMs with Comment Augmentation"
  https://aclanthology.org/2024.findings-acl.809/
  https://arxiv.org/abs/2402.13013
  *Key finding (cited in script): Increasing NL comment density in code training data improved HumanEval from 16.46 to 23.17 (+41%) and MBPP from 19.00 to 29.20 (+54%). Model trained on comment-augmented data outperformed even the stronger model that generated the comments. NL comments serve as alignment bridge between model's deep NL knowledge and code generation.*

- **ICLR 2025 Workshop** — "At Which Training Stage Does Code Data Help LLMs Reasoning?"
  https://openreview.net/forum?id=KIPJKST4gw
  *Key finding: Code + text pre-training significantly enhances NL reasoning with almost no negative transfer. Replacing 10% of web code with high-quality synthetic code: +9% NL reasoning, +44.9% code benchmarks. Relationship is bidirectional—code and NL are mutually reinforcing.*

- **VentureBeat** — "Code in pre-training data improves LLMs performance at non-coding tasks" (2024)
  https://venturebeat.com/ai/code-in-pre-training-data-improves-llms-performance-at-non-coding-tasks/

- **FSE 2025** — "Natural Language Outlines for Code: Literate Programming in the LLM Era"
  https://arxiv.org/abs/2408.04820
  *Key finding: NL outlines of code functions enable bidirectional sync (change NL → regenerate code, or vice versa). Professional developers rated 60% of LLM-generated outlines as "excellent." Directly validates the PDD model of NL specification governing generated code.*

### LLM Training Data Composition (Code vs Natural Language)

- **Educating Silicon** — "How much LLM training data is there, in the limit?" (2024)
  https://www.educatingsilicon.com/2024/05/09/how-much-llm-training-data-is-there-in-the-limit/
  *Key data: The Stack v2 (largest public code dataset): ~775B tokens. RefinedWeb (text): 5T+ tokens. Llama 3: 15T total tokens. Llama 4: 30T+ tokens. Code represents roughly 3-8% of pre-training tokens for general-purpose models—approximately 12-30× more NL than code in the training mix.*

- **Meta** — "Introducing Meta Llama 3" (2024)
  https://ai.meta.com/blog/meta-llama-3/
  *Key data: 15T token training set. 4× more code than Llama 2, but exact code percentage not disclosed. Over 5% non-English data.*

### LLM Code Verification Limitations

- **ASE 2025** — "Uncovering Systematic Failures of LLMs in Verifying Code Against Natural Language Specifications"
  https://arxiv.org/abs/2508.12358
  *Key finding: LLMs systematically misjudge whether code matches NL specifications. More complex prompting actually increased misjudgment rates. LLMs can be misled by plausible NL—they sometimes trust NL descriptions over actual code semantics. Relevant caveat for PDD: poorly written prompts could generate confidently wrong code.*

---

## Chip Design Analogy (Schematics → Verilog → Synthesis)

### Historical Transition

- **Digilent** — "Verilog HDL Background and History"
  https://digilent.com/reference/learn/fundamentals/digital-logic/verilog-hdl-background-and-history/start
  *Key facts (cited in script): Verilog introduced by Gateway Design Automation in 1985. Represented "tremendous productivity improvement" over schematic capture. Became IEEE standard 1364-1995.*

- **Wikipedia** — "Electronic design automation"
  https://en.wikipedia.org/wiki/Electronic_design_automation
  *Key facts (cited in script): Prior to EDA, ICs were designed by hand. In the early 1970s, placement and routing tools emerged. Logic synthesis in the late 1980s changed methodology radically. Modern chips have billions of components—EDA tools are essential.*

- **Wikipedia** — "Hardware description language"
  https://en.wikipedia.org/wiki/Hardware_description_language
  *Key facts (cited in script): In 1990, vast majority of designs were schematic-based. By mid-1990s, roughly half used HDLs. Today, all but the most trivial designs use HDL. HDL simulation increased design capacity from hundreds to thousands of transistors.*

- **Accellera Systems Initiative** — "The Next IC Design Methodology Transition Is Long Overdue"
  https://www.accellera.org/resources/articles/icdesigntrans
  *Key facts (cited in script): Current RTL-based methodologies have reached their limits. 24+ (>50%) of world's leading semiconductor companies have begun HLS adoption. ST Micro: 90% of new digital IP development starts at behavioral level. Each methodology transition follows the same arc: initial resistance, gradual adoption by leaders, rapid industry-wide shift.*

### Synthesis Non-Determinism

- **WPI** — "RTL Synthesis" (Advanced Digital Systems Design, Fall 2024)
  https://schaumont.dyn.wpi.edu/ece574f24/04synthesis.html
  *Key facts: Different synthesis tools may interpret Verilog differently. Different synthesis software packages give different output results for the same input. Synthesized netlist may exhibit unexpected changes due to logic optimization.*

- **ChipVerify** — "Verilog Synthesis"
  https://www.chipverify.com/verilog/verilog-synthesis
  *Key context: Synthesis tools use heuristic optimization with ~1,500 random recipe variations per IP block.*

### Formal Equivalence Checking (The Toolchain Solution)

- **Synopsys** — "What is Equivalence Checking?"
  https://www.synopsys.com/glossary/what-is-equivalence-checking.html
  *Key facts (cited in script): Uses mathematical modeling techniques to prove two representations exhibit the same behavior. Formal proof approach—not sampling-based. Covers every possible input combination. Works across representations: RTL-to-gate (R2G), gate-to-gate (G2G).*

- **Synopsys** — "Formality Equivalence Checking"
  https://www.synopsys.com/implementation-and-signoff/signoff/formality-equivalence-checking.html
  *Key facts: Formality works closely with Design Compiler. Guidance from implementation stage simplifies verification. Designers no longer need to disable optimizations to get equivalence checking to pass.*

- **Synopsys Datasheet** — "Formality and Formality Ultra"
  https://www.synopsys.com/content/dam/synopsys/implementation&signoff/datasheets/formality-and-formality-ultra-ds.pdf

- **Wikipedia** — "Formal equivalence checking"
  https://en.wikipedia.org/wiki/Formal_equivalence_checking
  *Key distinction (cited in script): Formal equivalence checking provides mathematical proof. The problem with simulation-based checking is that quality is only as good as the test cases. Software tests are simulation-based (samples), not formal proofs.*

- **Cadence** — "Logic Equivalence Checking"
  https://www.cadence.com/en_US/home/explore/logic-equivalence-checking.html
  *Key context: LEC ensures gate-level netlist is functionally equivalent to RTL. Essential to confirm optimization and synthesis did not introduce errors.*

---

## Spec-Driven Development: Industry Convergence (2025)

- **Thoughtworks** — "Spec-driven development: Unpacking one of 2025's key new AI-assisted engineering practices" (Dec 2025)
  https://www.thoughtworks.com/en-us/insights/blog/agile-engineering-practices/spec-driven-development-unpacking-2025-new-engineering-practices
  *Key claim (cited in script): SDD inverts traditional architecture—specifications become executable and authoritative. Generated code is disposable, regenerable, replaceable. "The specification is the system of record, not the code."*

- **Martin Fowler / Thoughtworks** — "Understanding Spec-Driven-Development: Kiro, spec-kit, and Tessl"
  https://martinfowler.com/articles/exploring-gen-ai/sdd-3-tools.html
  *Key analysis: Evaluates three SDD tools. Notes specs are "refined context" that provides just enough information without overwhelming the model.*

- **InfoQ** — "Spec Driven Development: When Architecture Becomes Executable" (2025)
  https://www.infoq.com/articles/spec-driven-development/
  *Key claim: Runtime behavior becomes architecturally deterministic rather than emergent.*

- **GitHub** — "spec-kit" (open-source CLI, released Sep 2025)
  https://github.com/github/spec-kit
  *Key context (cited in script): GitHub released spec-kit for creating specification files. Released at version 0.0.30+.*

- **The New Stack** — "Spec-Driven Development: The Key to Scalable AI Agents" (2025)
  https://thenewstack.io/spec-driven-development-the-key-to-scalable-ai-agents/
  *Key claim: Specs are "refined context" that provide just enough information to be effective without overwhelming the model.*

- **Red Hat Developer** — "How spec-driven development improves AI coding quality" (2025)
  https://developers.redhat.com/articles/2025/10/22/how-spec-driven-development-improves-ai-coding-quality

---

## Prompt-to-Code Ratio (PDD Empirical Observation)

- **Source:** PDD's own empirical data from production usage.
  *Key claim (cited in script): A prompt is 1/5 to 1/10 the size of the code it generates. This is not from an external study—it reflects PDD's internal measurement across real modules. The ratio depends on module complexity: simpler CRUD modules trend toward 1:10; modules with complex business logic trend toward 1:5.*

---

## Module Size and Defect Density

- **Verma et al.** — "An Improved Approach for Reduction of Defect Density Using Optimal Module Sizes" (Hindawi, 2014)
  https://www.hindawi.com/journals/ase/2014/803530/
  https://onlinelibrary.wiley.com/doi/10.1155/2014/803530
  *Key finding (cited in script): Relationship between module size and defect density is curvilinear (U-shaped). Too small increases interface overhead; too large increases complexity. Lowest defect density at ~250 lines in Ada study. Optimal size depends on language, project, and environment.*

- **Hatton** — "Reexamining the Fault Density–Component Size Connection" (IEEE Software, 1997)
  https://ieeexplore.ieee.org/document/585176
  *Key finding: 200-400 line modules have lowest defect density (the "Goldilocks zone").*

---

## Manufacturing Analogy (Injection Molding)

- **Crescent Industries** — "The History of Injection Molding: A Transformative Journey"
  https://www.crescentind.com/blog/the-history-of-injection-molding-a-transformative-journey
  *Key claim: John W. Hyatt patented celluloid process in 1868. First injection molding machine patented 1872. James Hendry's screw injection machine revolutionized the field in 1946.*

- **HiTop Industrial** — "Injection Molding in the Textile and Fashion Industry"
  https://hitopindustrial.com/injection-molding-in-the-textile-and-fashion-industry/
  *Note: Injection molding is a plastics technique, only recently explored in textiles. The video uses it as a cross-industry analogy, not as an explanation for clothing manufacturing changes.*

---

## Generational Terminology

- **Genealogy Explained** — "How to Count Generations in a Family Tree"
  https://www.genealogyexplained.com/how-to-count-generations-in-a-family-tree/
  *Key claim: Great-grandparents are 3 generations back (~75-90 years). At 25-30 years per generation, a great-grandmother active in the 1960s is plausible for viewers aged 25-35.*
