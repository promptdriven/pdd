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

### Individual Task Speedup: 55%

- **GitHub Blog** — "Research: Quantifying GitHub Copilot's Impact on Developer Productivity and Happiness" (2022)
  https://github.blog/news-insights/research/research-quantifying-github-copilots-impact-on-developer-productivity-and-happiness/
  *Key finding: Developers completed tasks 55% faster with Copilot (P=.0017, 95% CI: 21-89%). Task: implement an HTTP server in JavaScript.*

- **arXiv** — "The Impact of AI on Developer Productivity: Evidence from GitHub Copilot" (Peng et al., 2023)
  https://arxiv.org/abs/2302.06590
  *Key finding: Treatment group completed task 55.8% faster. Less experienced programmers benefited more.*

### Overall Throughput: No Significant Change

- **Visual Studio Magazine** — "Another Report Weighs In on GitHub Copilot Dev Productivity" (Uplevel study, 2024)
  https://visualstudiomagazine.com/articles/2024/09/17/another-report-weighs-in-on-github-copilot-dev-productivity.aspx
  *Key finding: 800 developers. No significant improvement in cycle time or PR throughput. 41% increase in bugs.*

- **METR** — "Measuring the Impact of Early-2025 AI on Experienced Open-Source Developer Productivity" (2025)
  https://metr.org/blog/2025-07-10-early-2025-ai-experienced-os-dev-study/
  *Key finding: Randomized controlled trial. AI actually increased completion time by 19% for experienced developers on familiar codebases. Developers predicted it would help by 24%.*

- **arXiv** — "Measuring the Impact of Early-2025 AI on Experienced Open-Source Developer Productivity"
  https://arxiv.org/abs/2507.09089
  *Key finding: 16 experienced developers, 246 tasks, 140+ hours of screen recordings. Five key contributors to slowdown identified.*

### Code Quality Degradation

- **GitClear** — "AI Copilot Code Quality: 2025 Data Suggests 4x Growth in Code Clones" (2025)
  https://www.gitclear.com/ai_assistant_code_quality_2025_research
  *Key finding: AI-assisted coding leads to 4x more code cloning, increasing maintenance effort and technical debt.*

- **Stack Overflow** — 2025 Developer Survey: AI Section
  https://survey.stackoverflow.co/2025/ai
  *Key finding: Only 52% of developers agree AI tools have had a positive effect on productivity. Sentiment dropped to 60%, down from 70%+ in 2023-2024.*

### Enterprise Field Studies (More Moderate Gains)

- **MIT / Microsoft & Accenture** — "The Productivity Effects of Generative AI: Evidence from a Field Experiment with GitHub Copilot"
  https://mit-genai.pubpub.org/pub/v5iixksv
  *Key finding: 1,974 developers. 13-22% more PRs/week at Microsoft, 8-9% at Accenture. Does not account for quality/debt tradeoffs.*

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
