# Prompt-Driven Development - TTS Script

## Annotations Key

- `[TONE: ...]` - Overall vocal quality
- `[PACE: ...]` - Speaking speed
- `[PAUSE: Xs]` - Pause duration
- `**word**` - Strong emphasis
- `*word*` - Light emphasis
- `[EMOTION: ...]` - Emotional coloring

---

## COLD OPEN (0:00 - 2:00)

[TONE: casual, observational]
[PACE: moderate]

If you use Cursor, or Claude Code, or Copilot...

[PAUSE: 1s]

[TONE: slightly impressed]
...you're getting *really* good at this.

[PAUSE: 2s]

[TONE: knowing, conspiratorial]
[PACE: slightly slower]
But here's what your **great-grandmother** figured out... sixty years ago.

[PAUSE: 1.5s]

[TONE: matter-of-fact, dry]
When socks got cheap enough... [PAUSE: 0.5s] she *stopped*.

[PAUSE: 2s]

[TONE: direct, punchy]
Code just got that cheap.

[PAUSE: 1.5s]

[TONE: challenging, curious]
So why are we still **patching**?

[PAUSE: 1s]

[TONE: intriguing, slightly provocative]
What if there were a **compiler** — not for code, but for *prompts*?

---

## THE THIRTY-SECOND DEMO (2:00 - 2:30)

[PAUSE: 1.5s]

[TONE: direct, demonstrative]
[PACE: crisp, purposeful]
Watch this.

[PAUSE: 1.5s]

[TONE: matter-of-fact]
Fifteen lines of prompt. Two hundred lines of generated code.

[PAUSE: 1s]

[TONE: building, satisfying]
Now a failing test. Regenerate. Bug **gone**. Not patched — *gone*. The test is a permanent wall. That bug can never come back.

[PAUSE: 1.5s]

[TONE: pivoting, inviting]
Now let me show you **why** this matters.

---

## PART 1: THE ECONOMICS OF DARNING (2:30 - 8:30)

[PAUSE: 2s]

[TONE: professorial, confident]
[PACE: steady]
This isn't nostalgia. It's **economics**.

[PAUSE: 1s]

[TONE: explanatory]
In 1950, a wool sock cost *real money* relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar.

[PAUSE: 0.8s]

[TONE: building momentum]
By the mid-1960s, the math **flipped**. A new sock cost *less* than the time to repair the old one. Darning became... [PAUSE: 0.5s] [TONE: slightly amused] *irrational*.

[PAUSE: 1.5s]

[TONE: pivoting, direct]
Now look at **code**.

[PAUSE: 1s]

[TONE: historical, sweeping]
For *decades*, generating new code was expensive. Writing from scratch took hours, days, *weeks*. So when something broke, you patched. [PAUSE: 0.3s] Of *course* you patched. [PAUSE: 0.3s] It was rational.

[PAUSE: 1.5s]

[TONE: acknowledging, fair]
Now, here's where it gets interesting. AI made patching faster *too*. Cursor, Claude Code, Copilot—they're **incredible** tools. They understand your codebase, suggest fixes, catch bugs before you make them.

[PAUSE: 1s]

[TONE: validating]
Look—each patch is getting *faster*. That's **real**. That's what you feel when you use these tools.

[PAUSE: 1.5s]

[TONE: pivoting to reveal]
But watch the *dashed* line. The **total** cost. It's barely moving.

[PAUSE: 1s]

[TONE: explaining the paradox]
Because even though each patch is faster, every patch still leaves *residue*. Technical debt. And that debt accumulates—**faster** now, because you're patching faster.

[PAUSE: 1.5s]

[TONE: stark, data-driven]
GitHub measured a **fifty-five percent** speedup on individual coding tasks. But that was ninety-five developers writing one HTTP server from scratch. A greenfield task—exactly where AI shines.

[PAUSE: 1s]

[TONE: contrasting, serious]
When Uplevel tracked almost **eight hundred** developers across real enterprise work for a full year? No change in throughput. **Forty-one percent** more bugs. The Uplevel team themselves expected to see gains. Their own product manager said: [PAUSE: 0.3s] [TONE: quoting] *"People are ending up being more reviewers for this code than in the past, and you might have some false faith that the code is doing what you expect."*

[PAUSE: 1.5s]

[TONE: building the case]
And GitClear confirmed it across **two hundred eleven million** lines of code. Since AI coding assistants arrived, code churn is up **forty-four percent**—new code getting revised within two weeks. Meanwhile, refactoring collapsed by **sixty percent**. Developers aren't cleaning up. They're *piling on*.

[PAUSE: 2s]

### CONTEXT ROT

[TONE: revealing something new]
And there's something *else* hiding in that debt. Something specific to **AI-assisted** development.

[PAUSE: 1.5s]

[TONE: setting up the concept]
When your codebase is *small*, AI tools are **brilliant**. The context window—what the model can actually *see*—covers almost everything. It understands how the pieces connect.

[PAUSE: 1.5s]

[TONE: building tension]
[PACE: slightly slower]
But codebases *grow*. And that window? [PAUSE: 0.5s] It stays the **same size**. A typical enterprise codebase spans *millions* of tokens. Even the largest context windows hold a fraction of that.

[PAUSE: 1.5s]

[TONE: analytical]
So now the AI has to *guess* what's relevant. Tools like Cursor use embeddings. Claude Code uses agentic search—grep, file by file. When Jolt AI benchmarked these tools on real codebases like Django and Kubernetes, pure vector search *failed* to find the right files. Agentic search found more—but took **three to five minutes** per query.

[PAUSE: 1.5s]

[TONE: escalating]
And here's what makes it worse. A 2025 EMNLP study proved that even when the model retrieves the *right* information, performance still degrades—**fourteen to eighty-five percent**—just from the sheer length of the input. It's not about finding the right code. The extra tokens *themselves* hurt the model's ability to reason. A separate Chroma study across eighteen state-of-the-art models confirmed the pattern—they call it *context rot*.

[PAUSE: 2s]

[TONE: pivoting, analytical]
This is why AI-assisted patching is really **two** stories — and why every productivity study seems to *contradict* every other one.

[PAUSE: 1s]

[TONE: clarifying, resolving a mystery]
The GitHub study measured greenfield, in-distribution work — exactly where AI shines. The METR study measured brownfield, out-of-distribution work — where AI *flounders*. They're not contradictory. They're measuring different **quadrants**. And most real enterprise work? [PAUSE: 0.5s] It lives in the bottom-right.

[PAUSE: 1.5s]

[TONE: validating]
On a *small* codebase—a few thousand lines—patching with AI is genuinely transformative. The context window covers everything. That's **real**.

[PAUSE: 1s]

[TONE: contrasting, serious]
But on a *large* codebase—the kind you get after years of patching—experienced developers are actually **nineteen percent** *slower* with AI tools. [PAUSE: 0.5s] And here's the devastating part: those same developers *believed* AI was making them **twenty percent** *faster*. That's a **thirty-nine point** gap between what it felt like and what happened. The context window can't keep up. The model guesses wrong. But it guesses *confidently*—so you don't notice until the bugs hit production.

[PAUSE: 1.5s]

[TONE: the trap revealed]
And here's the catch: every patch makes the codebase **bigger**. So patching pushes you from the world where AI *helps*... into the world where it **doesn't**.

[PAUSE: 2s]

[TONE: solution emerging]
Regeneration doesn't have this problem. A prompt is a *fifth* to a *tenth* the size of the code it governs. So where raw code overwhelms the context window, the *prompts* for ten modules fit comfortably. And the prompt defines its own context—the developer declares exactly what the model needs to see, instead of an agentic tool guessing at what's relevant. No retrieval. No search. No *rot*.

[PAUSE: 1.5s]

[TONE: insightful, building]
And there's something else. These models are trained on up to **thirty times** more natural language than code. Natural language is their deepest fluency. MIT showed that giving models natural language context for coding tasks improved performance by up to **eighty-nine percent**. A prompt *is* natural language. You're speaking the model's strongest language and giving it room to think.

[PAUSE: 1.5s]

[TONE: storytelling, concrete]
A team optimizing ad delivery latency had **twenty** modules on the critical path. As code? They overflowed the context window. As prompts — a fifth to a tenth the size — they *all* fit. The team optimized the entire critical path in prompt space and exceeded their half-millisecond latency target.

[PAUSE: 1s]

[TONE: precise]
Research also confirms: modules around **two hundred fifty** lines have the *lowest* defect density—a U-shaped curve where too small fragments logic and too large explodes complexity. That's exactly the size a focused prompt produces.

[PAUSE: 1.5s]

[TONE: significant, emphatic]
[PACE: slightly slower]
Meanwhile, generation just crossed below **both** lines. The debt doesn't just slow down—it *resets*. Each regeneration starts clean.

[PAUSE: 2s]

[TONE: appreciative but pivoting]
Tools like Cursor and Claude Code are the best darning needles **ever made**. I *use* them. They're fantastic.

[PAUSE: 1s]

[TONE: pointed, landing the blow]
But they're still **darning needles**. And the fundamental problem with darning isn't *speed*—it's **accumulation**.

[PAUSE: 1.5s]

[TONE: revealing a secret]
[PACE: slightly slower for emphasis]
This is the part of software economics *nobody talks about*. **Eighty to ninety percent** of software cost isn't building the initial system.

[PAUSE: 1s]

[TONE: driving home the point]
It's *maintaining* it. McKinsey found that organizations with high technical debt spend **forty percent** more on maintenance and deliver features **twenty-five to fifty percent** slower. Stripe measured developers wasting a *third* of their entire work week on technical debt and maintenance.

[PAUSE: 1s]

[EMOTION: ominous but hopeful]
And those costs **compound**—literally. Technical debt follows a compound interest curve. [PAUSE: 0.8s] Unless you regenerate. Then the debt resets.

[PAUSE: 2s]

### THE KEY INSIGHT

[TONE: deliberate, signaling importance]
[PACE: slower, weighted]
Now here's the thing I want you to **take away** from everything I've just shown you.

[PAUSE: 1.5s]

[TONE: posing a question, building curiosity]
What if you could take the **same LLM** you're using today — same model, same parameters — and make it **dramatically** better at coding?

[PAUSE: 1.5s]

[TONE: revelatory, building]
[PACE: measured, giving each point weight]
Working in prompt space gives you **two** things at once. First: prompts are a fifth to a tenth the size of the code they govern. So your effective context window is **five to ten times** larger. Every token in that window is author-curated — no system prompts eating space, no retrieval tool guessing wrong. The *entire* context window is devoted to your problem.

[PAUSE: 1s]

[TONE: building further]
Second: these models were trained on up to **thirty times** more natural language than code. Natural language is their deepest fluency. MIT showed giving models natural language context improves coding accuracy by up to **eighty-nine percent**.

[PAUSE: 1.5s]

[TONE: emphatic, landing it]
[PACE: slower]
You get a **bigger** window AND a **smarter** model. That's not an incremental improvement. That's a **category shift**.

[PAUSE: 2s]

[TONE: challenging, personal]
Don't take my word for it. Take your favorite LLM, give it a hard coding problem as code, then give it the same problem described in natural language. The natural language version will **win**. [PAUSE: 0.5s] Every time.

---

## PART 2: THE PARADIGM SHIFT (8:30 - 13:00)

[PAUSE: 2s]

[TONE: curious, investigative]
There's a pattern here that shows up across industries. Not just cheaper materials—a deeper shift in *how things are made*.

[PAUSE: 1s]

[TONE: revelatory]
Consider injection molding. Before it existed, you crafted individual objects. After it? [PAUSE: 0.5s] You designed **molds**.

[PAUSE: 1.5s]

[TONE: building wonder]
[PACE: accelerating slightly]
Make the mold *once*, produce unlimited identical parts. Refine the mold *once*, every future part improves **automatically**.

[PAUSE: 1.5s]

[TONE: setting up the insight]
And when there's a defect?

[PAUSE: 1s]

[TONE: key insight, slower]
[PACE: deliberate]
You don't patch individual parts. You fix **the mold**. And that fix applies to *every part* you'll ever make again.

[PAUSE: 2s]

[TONE: philosophical, important]
This is the *real* shift. Not "cheaper material." A migration of where **value** lives.

[PAUSE: 1.5s]

[TONE: contrasting]
In crafting, value lives in *the object*. You protect the object. Losing the chair is losing **everything**.

[PAUSE: 0.8s]

In molding, value lives in *the specification*—the mold. The plastic part? [PAUSE: 0.3s] [TONE: dismissive] Disposable. Regenerate it at will.

[PAUSE: 2s]

[TONE: pivoting to new example]
And it's not just plastics. The chip industry hit this **exact** wall.

[PAUSE: 1.5s]

[TONE: historical, storytelling]
In the 1980s, chip designers drew every gate by hand. When transistor counts hit tens of thousands, they couldn't keep up. So in 1985, they moved up—from schematics to **Verilog**. A hardware description language. You described what you wanted the chip to *do*, and a synthesis tool generated the gates.

[PAUSE: 1.5s]

[TONE: building to key insight]
But here's the thing: synthesis was **non-deterministic**. Run it twice, get different gates. Different wiring. Different layout. The output varied every single time.

[PAUSE: 1.5s]

[TONE: resolving]
What Synopsys did was wrap a **verification toolchain** around the generator. Formal equivalence checking—using SAT and SMT solvers to produce mathematical proof that the output, whatever it looked like, behaved identically to the spec. The gates were different every time. The *function* was the same every time.

[PAUSE: 1s]

[TONE: crystallizing the analogy]
Synopsys Design Compiler was **GCC** for hardware descriptions. PDD is **GCC** for prompts.

[PAUSE: 2s]

[TONE: sweeping, historical]
[PACE: measured]
By 1990, most designs were still schematic-based. By the mid-1990s, half had switched. Today, all but the most trivial chips use HDL. Every time component counts exceeded what the current abstraction could handle, the industry moved up a level. The designer stopped specifying *how*... and started specifying **what**.

[PAUSE: 1.5s]

[TONE: building to a powerful realization]
[PACE: slightly slower]
Today, a modern chip has **billions** of gates. Nobody reviews the netlist. It's *impossible*. The abstraction isn't just convenient — it's **physically necessary**.

[PAUSE: 1.5s]

[TONE: drawing the parallel, serious]
We're hitting the **same wall** with AI-generated code. When AI generates ten thousand lines in a day, code review becomes **netlist review**. The question isn't whether you *should* review it. It's whether you *can*.

[PAUSE: 2s]

[TONE: connecting the threads]
[PACE: slightly slower]
This is that same transition. For **software**.

[PAUSE: 1.5s]

[TONE: crystallizing the metaphor]
The prompt is your mold. The code is just... *plastic*. And just like chip synthesis—the code is different every generation. But the tests lock the behavior. The process is **deterministic**.

---

## PART 3: THE MOLD HAS THREE PARTS (13:00 - 18:30)

[PAUSE: 2s]

[TONE: getting technical, engaged]
Now let's get *precise*. Because "prompt is the mold" is a nice metaphor, but it's incomplete.

[PAUSE: 0.8s]

In PDD, the mold has **three** components. Three types of capital you're accumulating.

### TEST CAPITAL

[PAUSE: 1.5s]

[TONE: introducing key concept]
First: **tests**. Tests are the *walls* of your mold.

[PAUSE: 1s]

[TONE: explanatory, visual]
Each test is a constraint. A boundary the generated code *cannot* cross.

[PAUSE: 1s]

[TONE: data-driven, serious]
And these walls matter more than you'd think. CodeRabbit analyzed hundreds of pull requests and found AI-generated code produces **one-point-seven times** more issues than human code—**seventy-five percent** more logic errors, **eight times** more performance problems. The 2025 DORA report confirmed it: AI without strong tests increases instability. AI *with* strong tests **amplifies** delivery.

[PAUSE: 1.5s]

[TONE: emphatic]
The walls aren't optional. They're what make regeneration *safe*. When the model generates code, it *sees* these tests. The code it produces must pass them. It literally **cannot** generate code that violates these walls.

[PAUSE: 1.5s]

[TONE: setting up scenario]
Now here's where it gets interesting. When you find a bug...

[PAUSE: 1s]

[TONE: key insight, emphatic]
...you don't patch the code. You add a **wall**.

[PAUSE: 1s]

[TONE: satisfying, resolving]
That wall is *permanent*. That bug can **never** occur again—not in this generation, not in *any* future generation.

[PAUSE: 1.5s]

[TONE: building excitement]
[PACE: slightly faster]
This is the **ratchet effect**. Tests only accumulate. The mold only gets more *precise*. Each wall you add constrains **all** future generations.

[PAUSE: 1.5s]

[TONE: comparative, driving home]
In traditional development, a bug fix helps *one place*. In PDD, a test prevents that bug **everywhere**, **forever**.

[PAUSE: 1.5s]

[TONE: clarifying, precise]
And sometimes the bug isn't in the code — it's in the **prompt**. The code *correctly* implements a wrong specification. PDD distinguishes between these. A code bug? Add a wall. A prompt defect? Change the **mold itself**.

[PAUSE: 1.5s]

[TONE: preemptive, honest]
Now — you might be thinking: "But LLMs don't follow instructions **reliably**." [PAUSE: 0.5s] You're right. *Today*. But PDD doesn't need perfection on every run. Generate **five** versions. Pick the one that passes all tests. The walls don't care how many attempts it took.

[PAUSE: 1.5s]

[TONE: brief, authoritative]
And some of those walls aren't just tested — they're *proven*. PDD uses Z3, the same class of SMT solver that the chip industry uses for formal equivalence checking, to mathematically prove that properties hold for **every possible input**. Not sampling. Mathematical **proof**. The chip design analogy isn't a metaphor. It's the **same technology**.

### PROMPT CAPITAL

[PAUSE: 2s]

[TONE: moving to next concept]
Second: the **prompt**. Your specification of what you want.

[PAUSE: 1s]

[TONE: clarifying]
The prompt doesn't define the walls—tests do that. The prompt defines what you're *asking for* and *why*.

[PAUSE: 1s]

[TONE: subtle, insightful]
And here's something subtle: the exact implementation can *vary*. What's locked is the **behavior**. The code is flexible; the contract is fixed.

[PAUSE: 1s]

[TONE: practical wisdom]
A good prompt is a *fifth* to a *tenth* the size of the code it generates. Think of the prompt as your **header file**. The generated code is the OBJ file. You're specifying *what* and *why*... not *how*. And that compression matters.

[PAUSE: 1.5s]

[TONE: connecting to earlier insight]
Remember the context window problem? Code is token-expensive. But prompts are natural language—and these models were trained on up to **thirty times** more natural language than code. Researchers found that just adding natural language comments to code training data improved generation quality by **forty-one percent**. The prompt isn't fighting the model's strengths. It's *leveraging* them.

[PAUSE: 1s]

[TONE: precise]
And unlike agentic tools that dynamically guess which code to load into context—and increasingly guess *wrong*—each prompt declares its own dependencies. The context is **author-defined**, not machine-assembled. Every token in that window is author-curated. No system prompts eating space. No retrieval tool guessing wrong. The *entire* context window is devoted to your problem.

### GROUNDING CAPITAL

[PAUSE: 2s]

[TONE: introducing third concept]
Third: **grounding**. This determines the *properties* of what fills the mold.

[PAUSE: 1s]

[TONE: explanatory]
Grounding is learned from your past generations. When you successfully generate and fix code, that knowledge feeds **back** into the system.

[PAUSE: 0.8s]

Your style. Your patterns. Your team's conventions. Grounding captures all of it and applies it *automatically* to future generations.

[PAUSE: 1.5s]

[TONE: synthesizing]
Prompt plus tests plus grounding. [PAUSE: 0.3s] Intent plus constraints plus style. [PAUSE: 0.3s] Together, they form a **complete specification**.

[PAUSE: 1s]

[TONE: precise, structural]
When these conflict, tests **win**. Always. The walls override the specification. The specification overrides the style.

[PAUSE: 1.5s]

[TONE: emphatic, memorable]
The code is *output*. The mold is what **matters**.

---

## PART 4: THE PRECISION TRADEOFF (18:30 - 21:00)

[PAUSE: 2s]

[TONE: intellectual, curious]
Here's something subtle that changes how you think about prompts.

[PAUSE: 1s]

[TONE: explanatory]
In 3D printing, there's no mold. The machine must know exactly where to place *every single point* of material. The specification must be *extremely* precise.

[PAUSE: 1s]

[TONE: contrasting]
In injection molding, precision comes from **the walls**. The material just flows until it's constrained.

[PAUSE: 1.5s]

[TONE: connecting to PDD]
This maps *directly* to PDD.

[PAUSE: 1s]

With few tests, your prompt needs to specify *everything*. Edge cases. Error handling. Exact behavior in every situation.

[PAUSE: 1s]

[TONE: liberating, positive]
With *many* tests, the prompt only needs to specify **intent**. The tests handle the constraints.

[PAUSE: 1.5s]

[TONE: insight landing]
This is why test accumulation matters. It's not just about catching bugs. It's about making prompts *simpler* and regeneration *safer* over time.

[PAUSE: 1s]

[TONE: memorable phrase]
The more walls you have, the less you need to specify. The **mold** does the precision work.

[PAUSE: 1.5s]

[TONE: honest, addressing skeptics head-on]
But some things genuinely need code-level precision. Algorithm choice. Performance-critical inner loops. Bit-level operations.

[PAUSE: 1s]

[TONE: resolving, practical]
PDD handles this. A prompt can embed code snippets for exactly those critical sections. It's not all-or-nothing. You stay in prompt space for as *long* as possible — architecture, intent, constraints, edge cases — then dip into code when the precision demands it.

[PAUSE: 1s]

[TONE: framing]
Think of it as a **spectrum**. Natural language on one end, code on the other. The question isn't "prompts *or* code." It's "how far into prompt space can you stay?" For most of the specification — further than you'd think.

---

## PART 5: COMPOUND RETURNS (21:00 - 23:15)

[PAUSE: 2s]

[TONE: strategic, analytical]
Let's talk about **compound returns**.

[PAUSE: 1s]

[TONE: describing the old way]
When you patch code, each fix has *local* returns. You fixed one bug in one place. Similar bugs can still occur elsewhere. And sometimes your patch introduces *new* bugs—CodeRabbit found AI patches carry **one-point-seven times** more issues than human code. So each patch risks creating *more* patches.

[PAUSE: 0.8s]

[TONE: dismissive]
The returns are linear at best. Often *sub*linear. And the cost keeps compounding—CISQ estimates technical debt costs US companies **one-point-five-two** *trillion* dollars annually.

[PAUSE: 1.5s]

[TONE: building to contrast]
When you add a test in PDD, the returns are **different**.

[PAUSE: 1s]

[TONE: building excitement]
[PACE: slightly faster]
That test you wrote *today*? It constrains tomorrow's generation. And next week's. And next *year's*. It's a **permanent wall**.

[PAUSE: 1.5s]

[TONE: summarizing powerfully]
Every investment in the mold has **compound** returns. Every investment in patching has **diminishing** returns.

[PAUSE: 2s]

[TONE: empathetic, reasonable]
Your great-grandmother wasn't *stupid* for darning socks. The economics made it rational.

[PAUSE: 0.8s]

[TONE: same empathy, present day]
And you're not *stupid* for patching code. Until now, the economics made it rational.

[PAUSE: 1.5s]

[TONE: pivotal, serious]
But the economics **changed**. And when economics change, behavior that was rational becomes... [PAUSE: 0.8s] [TONE: wry, pointed] darning socks.

[PAUSE: 1.5s]

[TONE: honest, self-aware, a touch of humor]
A researcher at Microsoft, after seeing PDD for the first time, said: [PAUSE: 0.5s] [TONE: quoting] *"This is either the way of the future or it's going to crash and burn spectacularly."* [PAUSE: 0.8s] [TONE: frank, confident] He's right — it's a contrarian bet. But the economics are on our side.

---

## CLOSING (23:15 - 25:00)

[PAUSE: 2s]

[TONE: wrapping up, reflective]
[PACE: measured, deliberate]
So here's the mental shift.

[PAUSE: 1.5s]

[TONE: practical, addressing the real concern]
Now — you don't work on a greenfield project. *Nobody* does.

[PAUSE: 1s]

[TONE: reassuring, concrete]
PDD can create prompts *from* existing code. Start with **one** module. Generate its prompt. Add tests. Regenerate. Compare. When the regenerated version passes all tests, the prompt is your new source of truth for that module.

[PAUSE: 1s]

[TONE: measured, reasonable]
One module at a time. No big bang. No rewrite. Just a gradual migration of where value lives — from code to *specification*.

[PAUSE: 2s]

[TONE: simple truth]
You don't patch socks because socks got cheap. The economics made patching irrational.

[PAUSE: 1.5s]

[TONE: direct, present]
Code just got that cheap.

[PAUSE: 2s]

[TONE: declarative, memorable]
[PACE: slower, giving each phrase weight]
Prompts encode *intent*.
[PAUSE: 0.5s]
Tests preserve *behavior*.
[PAUSE: 0.5s]
Grounding maintains *style*.

[PAUSE: 1.5s]

[TONE: accepting, matter-of-fact]
Code is generated, verified, and **disposable**.

[PAUSE: 2s]

[TONE: final thesis, weight]
[PACE: slow, deliberate]
The code is just *plastic*.

[PAUSE: 2s]

[TONE: conclusive, resonant]
The **mold**... is what matters.

[PAUSE: 3s]
[FADE OUT]

---

**Total runtime: ~24-26 minutes**
