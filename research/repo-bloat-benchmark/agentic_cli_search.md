# Background: How Agentic Coding CLIs Acquire Code Context

**Companion to:** [`design.md`](./design.md) — *Agentic Localization Degradation Under Repository Bloat* (issue [#1209](https://github.com/promptdriven/pdd/issues/1209), PR [#1419](https://github.com/promptdriven/pdd/pull/1419))
**Issue:** [#1430](https://github.com/promptdriven/pdd/issues/1430) — Context on Agentic CLI
**Status:** Background / related-work section (not part of the locked §10 pre-registration)
**Last updated:** 2026-06-05

> **Scope and role.** This document is the research-paper *background* the benchmark needs but [`design.md`](./design.md) deliberately does not carry: a precise, cited account of **how agentic coding CLIs locate code**, and **how that process differs across the tools practitioners actually use**. The benchmark measures *localization cost* and *how much irrelevant code reaches the model's context window* under irrelevant repository bloat ([`design.md` §6](./design.md#6-instrumentation-plan)); both are **outputs of the agent's search-and-read loop**, so the construct being measured is only as well-defined as our model of that loop.

---

## 1. Why the search mechanism is the object of study

The benchmark's research question is whether *irrelevant repository bloat increases localization cost and reduces hidden-test success for agentic code patching* ([`design.md` §1](./design.md#1-purpose-and-research-question)). "Localization cost" is not an intrinsic property of a task — it is the work an agent expends to **find the right code among the wrong code**. That work is performed by a concrete software process: a loop of tool calls (search, list, read) interleaved with model reasoning, terminating in an edit. Three consequences follow, each tying back to the design:

1. **The dependent variables are search-process observables.** `files_read_before_first_edit`, `search_or_tool_calls_before_first_edit`, `irrelevant_file_read_ratio`, and the in-context token metrics (`input_tokens_*`) ([`design.md` §6.1](./design.md#61-what-we-capture)) are all measurements *of the search loop*. Interpreting them requires knowing what a "search", a "read", and a "tool call" mean for the agent under test.

2. **The instrumentation must match the agent's retrieval substrate.** The locked filesystem tap (Linux container + OverlayFS + FUSE byte-extent reads, [`design.md` §6.2](./design.md#62-how-we-capture-it-defense-in-depth)) captures reads that cross the kernel — appropriate for an agent that *shells out* to `grep`/`ripgrep`/`cat`. It silently under-captures an agent whose "search" is an **embedding query answered server-side** (see §3, §6). This is the open item already flagged in [`design.md` §10, "Still to confirm" #2](./design.md#10-locked-decisions).

3. **External validity is bounded by the agent's retrieval family.** If bloat sensitivity is *mechanistically* a property of on-demand grep-and-read search, then a result obtained with Codex CLI may not transfer to an index- or embedding-based tool — and saying so precisely is more useful than a single headline number.

The remainder of this document supplies the vocabulary and evidence to make those three statements rigorous.

---

## 2. The agentic loop: search as an interactive, model-driven process

Modern coding agents do not retrieve context in a single pass and then answer. They run an **interactive control loop** — variously *ReAct* (reason–act–observe) or *think → tool-call → observe → repeat* — in which the model proposes an action, the environment executes it, the observation is appended to the transcript, and the model decides the next action, until it emits a final answer or edit [1, 3, 12]. OpenAI describes Codex CLI as exactly this single-agent loop driven by the Responses API [1, 3, 4]; the academic formalization is Yang et al.'s **Agent–Computer Interface (ACI)**, which argues that the *design of the search/navigation/edit commands the agent is given* — not just the underlying model — determines software-engineering performance [12].

Two properties of this loop matter for bloat:

- **Localization is incremental and stateful.** Context enters the model window *cumulatively*, observation by observation. A wrong turn (reading an irrelevant but plausible file) is not free: its tokens occupy the window for the rest of the run and can crowd out signal — the mechanism the "effective context window" claim names ([`design.md` §1](./design.md#1-purpose-and-research-question), [§7.2](./design.md#72-trend--slope-fits)). This is why the design keeps *what the agent read off disk* (FS tap → `irrelevant_file_read_ratio`, a read-**volume** signal) distinct from *what entered the model window* (transcript tap → `input_tokens_*`, the in-context token cost) ([`design.md` §6.1](./design.md#61-what-we-capture)): the loop is precisely where a file can be *visited but never surfaced into context*, or *surfaced and re-surfaced*. (PR [#1419](https://github.com/promptdriven/pdd/pull/1419) formalizes the in-context layer into a dedicated distractor-penetration metric family.)
- **The tools the agent is given bound what "search" can even mean.** An ACI that exposes `grep`, `find`, and `open` produces a fundamentally different cost curve under bloat than one that exposes a single `semantic_search(query) → top-k chunks` call. The next section makes this distinction the organizing axis.

---

## 3. A taxonomy of code-context acquisition

We group agents by **how candidate code reaches the model**, because that mechanism — not the brand — is what predicts bloat behavior. Three families, with hybrids increasingly common.

### Family A — Agentic / tool-based search (on-demand, no persistent index)

The model autonomously issues filesystem and text-search commands (`glob`/`grep`/`read`, or a shell that runs `ripgrep`), reads results, and decides what to search next, with reasoning between steps [5, 6, 16]. There is **no precomputed index and no embeddings**; the "index" is the live filesystem, queried lazily. Anthropic's Claude Code is the canonical example: it exposes `Grep`, `Glob`, and `Read` and explores on demand rather than indexing the repository [5, 6]; its content search is backed by `ripgrep` [7, 15]. Reportedly, an Anthropic engineer stated that in their testing "agentic search outperformed [RAG] by a lot, and this was surprising" [7]. OpenAI's Codex CLI is the same family: a ReAct loop whose primary tool is shell/`container.exec`, used to run search/read commands, with edits applied via `apply_patch`; it "doesn't appear to rely on pre-indexing" and "analyzes code on-demand" [1, 2, 4]. SWE-agent's ACI is the research instantiation: "tailored search and navigation commands that efficiently locate relevant files and content" [12].

*Cost signature under bloat:* search and read cost is **paid at run time and scales with the amount of plausible-but-irrelevant code** — more candidate matches per `grep`, more files worth opening, more tokens pulled into the window. Failure modes are *window dilution* and *wrong-file reads*. This family is the one the FUSE/OverlayFS tap captures natively, because its reads cross the kernel.

### Family B — Retrieval-augmented / index-based (precomputed, single-shot retrieval)

A background process builds a **persistent representation** of the repository, and retrieval is a (mostly) single-shot lookup against it. Two sub-mechanisms:

- **B1 — Embedding / vector retrieval.** Files are chunked, embedded, and stored in a vector database; a query is embedded and matched by nearest-neighbor. Cursor is the reference design: it "breaks your code into meaningful chunks…, converts each chunk into a vector embedding…, and stores the results in a vector database," computing embeddings **server-side** (chunks sent to Cursor's servers, embeddings stored with file paths and line ranges in a remote vector DB — historically Turbopuffer), with the index kept fresh by periodic sync (~5 min) and protected by obfuscation/encryption [10, 11]. Agentless's localization stage likewise uses embedding-based retrieval as one ingredient [13].
- **B2 — Symbolic / structural index (no embeddings).** A parsed-symbol graph stands in for embeddings. Aider builds a **repository map** with `tree-sitter`: it extracts definitions and references from every file, ranks them with a **PageRank over the symbol-reference graph**, and renders a **token-budgeted** summary of the highest-ranked signatures (default `--map-tokens` ≈ 1k) that is placed in the prompt [8, 9]. Graph-search localizers (e.g., iterative code-graph search) generalize this to a navigable dependency/call graph the agent walks [14].

*Cost signature under bloat:* in-context tokens are **capped by construction** (top-k chunks, or a fixed map-token budget), so the window does not flood. Instead, bloat **inflates the index and dilutes ranking**: more chunks/symbols compete for the same top-k or token budget, so the failure mode is *the right code falling out of the retrieved set* (a recall/precision failure), not window saturation. Crucially, much of the "search" here happens **off the local filesystem** (server-side embedding, in-memory graph), so a kernel FS tap under-observes it.

### Family C — Hybrid

Most mature tools now combine A and B and let the model choose. Cursor explicitly runs **both** semantic search and agentic `grep`, with the "Agent pick[ing] the right tool based on [the] prompt" — grep for specific symbols, embeddings for behavioral/conceptual queries, chained searches for complex exploration [10]. Agentless couples embedding- and prompt-based retrieval with LLM re-ranking in a **hierarchical** file → class/function → edit-location localization [13]. Codex and Claude Code are predominantly Family A but can be extended toward B via **MCP** servers (e.g., a semantic-search tool) [1, 5].

### Comparison

| Agent (CLI/tool) | Primary mechanism | Persistent index? | Search primitives | What enters the window | Where search runs | Family |
|---|---|---|---|---|---|---|
| **Codex CLI** (OpenAI) [1,2,4] | Agentic, ReAct loop | No (on-demand) | shell/`container.exec` → `grep`/`rg`/`find`/`ls`/`cat`; `apply_patch` for edits; optional web/MCP | Whatever the model reads/greps, cumulatively | Local FS (shells out) | A |
| **Claude Code** (Anthropic) [5,6,7] | Agentic search | No (explicitly no index/embeddings) | `Grep` (ripgrep), `Glob`, `Read`; subagents | Files/snippets the model opens | Local FS | A |
| **SWE-agent** (research) [12] | Agentic via ACI | No | ACI `search_file`/`search_dir`/`find_file`/`open`+`goto`/`scroll_*`; linted `edit` | Viewed/searched windows | Local FS (sandboxed) | A |
| **Aider** [8,9] | Symbolic repo map | Yes (tree-sitter + PageRank) | Ranked-tags map in prompt; user adds files to chat | Token-budgeted signature map (+ added files) | Local (parse + rank) | B2 |
| **Cursor** [10,11] | Embeddings + agentic grep | Yes (server-side vector DB) | `@codebase`/semantic search **and** grep; agent chooses | Top-k retrieved chunks and/or grep hits | **Server-side** embedding + local grep | C (B1+A) |
| **Agentless** (research) [13] | Hierarchical retrieval | Partly (embedding + prompts) | Embedding + prompt retrieval, LLM re-rank, no autonomous tool loop | Ranked files/functions/edit spans | Mixed | C (B+heuristics) |

(`ripgrep` is the shared text-search backbone for the Family-A tools [7, 15]; the rows above describe default behavior and are configuration- and version-dependent — see §7.)

### Concrete search primitives — the commands agents actually issue

Family A reduces, almost entirely, to a small set of POSIX text/file utilities invoked either directly (a shell tool) or through thin structured wrappers. The same four abstract operations recur — *discover files*, *search content*, *read a slice*, *navigate within a file* — and each agent realizes them with concrete commands. For a benchmark this matters concretely: every one of these read/search commands bottoms out in `open()`/`read()` syscalls that the FUSE tap logs ([`design.md` §6.2](./design.md#62-how-we-capture-it-defense-in-depth)), so the kernel tap captures them *regardless of which command the agent chose*, and it is exactly here that read **volume** diverges from in-context **tokens** (a `grep -r`/`rg` scan touches far more bytes than ever enter the window; a `sed -n`/`head` reads a slice that mostly does) — the read-volume-≠-tokens distinction in [`design.md` §6.1](./design.md#61-what-we-capture).

| Abstract operation | Typical shell commands (Codex CLI; Claude Code `Bash`; SWE-agent bash) [1,2,4,5,12] | Structured-tool form |
|---|---|---|
| **Discover files** (by name/glob) | `find . -name '*.py'`, `fd`, `ls -R`, `tree`, shell globs `**/*.py` | Claude Code `Glob`; SWE-agent `find_file`; Codex `@` fuzzy file search |
| **Search content** (by string/regex) | `rg -n 'symbol'`, `rg -l`, `grep -rn`, `grep -A/-B` for context, `ast-grep` (structural) | Claude Code `Grep` (ripgrep-backed [7]); SWE-agent `search_file` / `search_dir` (≤ 50 hits/query [12]); Cursor `grep` tool [10] |
| **Read a slice** (open part of a file) | `sed -n '120,180p' f.py`, `cat`/`cat -n`, `head -n`, `tail -n`, `awk 'NR>=120&&NR<=180'`, `wc -l` | Claude Code `Read` (offset/limit); SWE-agent `open` (100-line window [12]); Codex file read |
| **Navigate within a file** (move the window) | re-issue `sed -n`/`grep -n` at new line ranges | SWE-agent `goto` / `scroll_down` / `scroll_up` [12] |
| **Edit** (apply the fix) | in-place `sed -i`, `patch`, here-doc rewrites (shell agents that allow it) | Codex `apply_patch` [2,4]; Claude Code `Edit`/`Write`; SWE-agent `edit` (linter-validated [12]) |

Two clarifications matter for interpreting the benchmark:

- **`ripgrep` (`rg`) is the de facto content-search backbone.** It is what Claude Code's `Grep` tool runs [7, 15] and a default choice in shell agents [16]; it is fast and `.gitignore`-aware, which means an agent's *content* search is biased toward tracked source — relevant when distractors are regrown into the tracked tree ([`design.md` §5](./design.md#5-distractor-generation-strategy)). `grep`/`ast-grep` appear as fallbacks or for structural queries.
- **Structured tools are wrappers over the same primitives, with guardrails.** Claude Code's `Grep`/`Glob`/`Read` and SWE-agent's ACI (`search_file`, `search_dir`, `find_file`, `open`, `goto`, `scroll_*`, `edit`) wrap the utilities above but **cap output** (e.g., SWE-agent returns ≤ 50 search hits and a 100-line view per turn [12]) so a single command cannot dump an oversized file into the window. These caps are themselves a bloat-mitigation and a confound the design should record: an agent that pages through results via repeated `goto`/`scroll` (or repeated `sed -n`) inflates *read volume and tool-call counts* without proportionally inflating *in-context tokens* — visible directly in the [`design.md` §6.1](./design.md#61-what-we-capture) split.

**Family B/C bypass these commands for retrieval.** Aider issues none of the above to *locate* code — it ships a precomputed tree-sitter/PageRank map in the prompt and only reads files the user adds to the chat [8, 9]. Cursor's *semantic* path answers a `semantic_search(query)` against a server-side vector index rather than the local filesystem, falling back to local `grep` only when the agent chooses it [10]. Consequently their localization work is **largely invisible to a kernel FS tap** and must be observed at the tool/retrieval boundary instead (§6).

---

## 4. Per-agent profiles (mechanism, primitives, knobs)

**Codex CLI (OpenAI).** Open-source, implemented in Rust; runs a single-agent ReAct loop over the Responses API [1, 3, 4]. The model's lever on the repository is a **shell tool** (`container.exec`); code reading and searching are ordinary commands (`rg`, `grep`, `sed -n`, `cat`, `ls`, `find`) issued through it, and edits go through a structured `apply_patch` tool rather than free-form shell writes [2, 4]. It ships a first-party **web search** tool (cached by default; live via `--search`) and supports **MCP** servers for additional tools [2]. Exploration is **on-demand, not pre-indexed** [2, 4]. Sandbox: macOS **Seatbelt** profile / Linux **Docker + iptables**, restricting filesystem scope to the working directory and network to the model API [4] — which is exactly the isolation posture the benchmark's run-environment freeze assumes ([`design.md` §8.1.1](./design.md#811-run-environment-freeze-review-3)). *Benchmark relevance:* because Codex shells out, its searches and reads are **kernel-visible**, so the FUSE/OverlayFS tap captures them without an in-process shim ([`design.md` §6.2](./design.md#62-how-we-capture-it-defense-in-depth)); the open question is whether its transcript also exposes the *content* surfaced by those tools for token-level attribution ([`design.md` §10, "Still to confirm" #3](./design.md#10-locked-decisions)).

**Claude Code (Anthropic).** Agentic coding CLI whose retrieval is deliberately **index-free**: it uses `Read`, `Grep` (ripgrep-backed), and `Glob` to explore the tree on demand, and delegates large multi-file reads to **subagents** that run in isolated context windows [5, 6, 7]. Anthropic's guidance is organized around the constraint that "Claude's context window fills up fast, and performance degrades as it fills" [5] — i.e., the very degradation-under-irrelevant-context effect the benchmark probes. *Benchmark relevance:* the closest comparator to Codex in mechanism; an obvious second arm if the pilot is extended.

**Aider.** Pairs the model with a **repository map** rather than autonomous search: `tree-sitter` extracts defs/refs, a **PageRank** over the def→ref graph ranks symbols (with weight multipliers for mentioned/well-named identifiers and chat files), and a **token-budgeted** rendering of the top signatures is injected into the prompt (`--map-tokens`, default ≈ 1k) [8, 9]. The map is a *structural* index, not embeddings. *Benchmark relevance:* the in-context distractor dose is **bounded by the map budget**, so Aider would be expected to show a *different* bloat curve — degradation via ranking dilution, not window flooding (§5).

**Cursor.** IDE-integrated agent with **server-side embedding indexing** (chunk → embed → vector DB, periodic re-sync, obfuscated/encrypted storage) **plus** agentic grep, with the agent selecting per query [10, 11]. *Benchmark relevance:* a Family-C tool whose semantic retrieval **bypasses the local FS**, so a kernel FS tap would under-report its "reads"; faithfully instrumenting it requires capturing the retrieval query and returned chunks at the tool boundary (§6).

**Others (brief).** *Cline / Roo-Code / OpenHands* are open agent harnesses in Family A (tool-driven file read/search/edit loops, often over VS Code or a shell) and inherit its cost signature. *Graph-search localizers* (e.g., iterative code-graph search, OrcaLoca-style priority scheduling over a code graph) are Family B/C research systems that navigate a dependency/call graph instead of free-text grep [13, 14]. These are not profiled in depth here but fit the taxonomy directly.

---

## 5. Why the mechanism predicts bloat sensitivity (hypotheses)

Mapping the families onto the three quantities the instrumentation already distinguishes — distractor volume *on disk* ⊇ distractor files *visited* (FS tap → `irrelevant_file_read_ratio`) ⊇ distractor tokens *in context* (transcript tap → `input_tokens_*`) ([`design.md` §6.1](./design.md#61-what-we-capture)) — yields concrete, pre-registerable predictions. (PR [#1419](https://github.com/promptdriven/pdd/pull/1419) names the in-context layer explicitly as a distractor context-share metric, which makes H1/H2 directly testable.)

- **H1 (Family A — agentic search, e.g., Codex, Claude Code).** Localization cost and **the distractor share of the context window rise with distractor volume**: more plausible files match each search, more get opened, and their tokens accumulate in the window. Predicted signatures: positive slope of `input_tokens_per_run`, `files_read_before_first_edit`, and `irrelevant_file_read_ratio` vs. size `S` (and of the in-context distractor share where instrumented); failure classes skew to *window dilution* and *wrong-file reads* ([`design.md` §6.4](./design.md#64-failure-classification)). This is the family the pilot locks (Codex), and the family the hypothesis in [`design.md` §7.5](./design.md#75-conclusion-required-pre-committed-interpretation) is implicitly written for.

- **H2 (Family B — index/repo-map, e.g., Aider, Cursor-semantic).** **In-context tokens stay roughly flat** (capped by top-k / map budget), so the "effective context window" *flooding* story is weak; instead bloat **degrades retrieval precision** — the right code is crowded out of the retrieved set. Predicted signatures: near-flat in-context distractor share but rising *retrieval-miss* / `localization_miss` rate and falling `hidden_pass_rate` *without* a token-cost blow-up. This is exactly the "token usage rises only modestly while success collapses" case the issue flags and [`design.md` §7.5](./design.md#75-conclusion-required-pre-committed-interpretation) asks the report to call out.

- **H3 (Family C — hybrid).** Behavior is **routing-dependent**: outcomes track *which* tool the agent chose per step, so the dominant variable becomes tool-selection policy, and bloat sensitivity interpolates between H1 and H2.

The practical upshot: **"does repo bloat hurt agentic localization?" likely has different answers for different retrieval families**, and the difference is mechanistic, not incidental. That is the strongest argument for treating the locked single-Codex pilot as *stage one* and pre-registering a cross-agent arm (at minimum a second Family-A agent such as Claude Code, and one Family-B/C agent such as Aider or Cursor) before generalizing any headline claim.

---

## 6. Implications for the benchmark's instrumentation and validity

1. **The FS tap is correct for Family A, partial for Family B/C.** The kernel-level FUSE/OverlayFS tap ([`design.md` §6.2](./design.md#62-how-we-capture-it-defense-in-depth)) captures every `open`/`read` an agent makes *through the filesystem* — the right choice precisely because Codex and Claude Code shell out to `ripgrep`/`grep` and a wrapper shim would miss subprocess reads. But an embedding agent's semantic retrieval (Cursor) is answered **off the local FS** (server-side vectors), and a repo-map agent (Aider) reads files once at index time, not at query time. For those, "what the agent searched" lives at the **tool/retrieval boundary**, not the syscall boundary, and a cross-agent extension must add a **tool-call/transcript tap that records the retrieval query and the returned chunks** — an extension of the transcript tap in [`design.md` §6.2](./design.md#62-how-we-capture-it-defense-in-depth) (the same surfaced-content capture PR [#1419](https://github.com/promptdriven/pdd/pull/1419) requires for token-level penetration).

2. **Distractor classification still works, but "visited" changes meaning.** The post-hoc distractor/core classification ([`design.md` §6.2](./design.md#62-how-we-capture-it-defense-in-depth)) is mechanism-agnostic (it matches paths against the manifest). What differs is the *visited* set: for Family B it is "chunks/symbols admitted to the index/retrieval set," not "files opened at run time." The read-versus-context accounting must be re-stated per family so a flat result is attributed to the right layer.

3. **External-validity caveat to record in the methodology note.** Any cross-agent comparison must hold the *task, repo, and seed* fixed while varying the agent, and must report that **bloat sensitivity is conditioned on retrieval family** — otherwise a Codex-only result risks being over-generalized into a claim about "agentic coding" writ large. This belongs alongside the contamination and read-volume-≠-tokens caveats in [`design.md` §7.4](./design.md#74-methodology-note).

4. **It sharpens "Still to confirm" #2.** [`design.md` §10](./design.md#10-locked-decisions) asks whether Codex shells out (ripgrep) vs reads in-process. The taxonomy answers *why it matters*: shelling out keeps Codex in Family A and keeps the FS tap authoritative; an in-process or server-side retrieval path would move it (or a future agent) toward Family B/C and demand the tool-boundary tap of point 1.

---

## 7. Threats to validity and scope of these claims

- **Proprietary, moving targets.** Codex CLI, Claude Code, and Cursor are actively developed; tool sets, sandboxes, and indexing behavior change between releases. Every claim here is **pinned to the cited source and its date**; for the experiment, the agent build/version is frozen and fingerprinted ([`design.md` §8.1.1](./design.md#811-run-environment-freeze-review-3)), and any agent added in a cross-agent arm must be pinned identically.
- **Mixed source quality.** Where a vendor publishes mechanism details, we cite the **primary** source (OpenAI Codex docs [1, 2]; Anthropic engineering [5]; Cursor docs [10, 11]; Aider docs [8, 9]; the SWE-agent [12] and Agentless [13] papers). Some operational specifics (e.g., Codex's exact internal `apply_patch`/sandbox plumbing, the "agentic search > RAG" quote) come from **reverse-engineering write-ups and reported statements** [4, 6, 7, 16] and are labeled as such; they should be re-verified before being load-bearing in the paper.
- **Configuration dependence.** Defaults are reported; users can enable embeddings via MCP on a Family-A tool, shrink/grow Aider's map budget, or disable Cursor indexing. The taxonomy classifies *default* behavior, which is what a benchmark should pin and report.
- **Not a benchmark of the agents.** This section is *background*: it does not claim which agent is better, only how each *finds* code, so the pilot can interpret its measurements and scope its generalization honestly.

---

## References

All URLs accessed 2026-06-05.

1. OpenAI. *Codex CLI* (documentation). https://developers.openai.com/codex/cli
2. OpenAI. *Features — Codex CLI* (documentation). https://developers.openai.com/codex/cli/features
3. OpenAI. *Unrolling the Codex agent loop.* https://openai.com/index/unrolling-the-codex-agent-loop/
4. P. Schmid. *OpenAI Codex CLI, how does it work?* https://www.philschmid.de/openai-codex-cli
5. Anthropic. *Claude Code: Best practices for agentic coding* (Engineering). https://www.anthropic.com/engineering/claude-code-best-practices
6. Vadim. *Claude Code Doesn't Index Your Codebase. Here's What It Does Instead.* https://vadim.blog/claude-code-no-indexing
7. *Why Claude Code Chose ripgrep Over Vector Search.* Rust Trends. https://rust-trends.com/posts/ripgrep-claude-code/
8. Aider. *Building a better repository map with tree-sitter* (2023-10-22). https://aider.chat/2023/10/22/repomap.html
9. Aider. *Repository map* (documentation). https://aider.chat/docs/repomap.html
10. Cursor. *Semantic & Agentic Search / Codebase Indexing* (documentation). https://cursor.com/docs/context/codebase-indexing
11. Cursor. *Securely indexing large codebases.* https://cursor.com/blog/secure-codebase-indexing
12. J. Yang, C. E. Jimenez, A. Wettig, S. Yao, K. Narasimhan, O. Press. *SWE-agent: Agent-Computer Interfaces Enable Automated Software Engineering.* NeurIPS 2024. arXiv:2405.15793. https://arxiv.org/abs/2405.15793
13. C. S. Xia, Y. Deng, S. Dunn, L. Zhang. *Agentless: Demystifying LLM-based Software Engineering Agents.* 2024. arXiv:2407.01489. https://arxiv.org/abs/2407.01489
14. *Issue Localization via LLM-Driven Iterative Code Graph Searching.* 2025. arXiv:2503.22424. https://arxiv.org/abs/2503.22424
15. A. Gallant. *ripgrep* (`rg`) — recursive line-oriented search tool. https://github.com/BurntSushi/ripgrep
16. Morph. *Agentic Search: How Coding Agents Find the Right Code.* https://www.morphllm.com/agentic-search
