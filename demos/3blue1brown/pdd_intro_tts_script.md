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

---

## PART 1: THE ECONOMICS OF DARNING (2:00 - 5:00)

[PAUSE: 2s]

[TONE: professorial, confident]
[PACE: steady]
This isn't nostalgia. It's **economics**.

[PAUSE: 1s]

[TONE: explanatory]
In 1950, a wool sock cost *real money* relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar.

[PAUSE: 0.8s]

[TONE: building momentum]
By 1990, the math **flipped**. A new sock cost *less* than the time to repair the old one. Darning became... [PAUSE: 0.5s] [TONE: slightly amused] *irrational*.

[PAUSE: 1.5s]

[TONE: pivoting, direct]
Now look at **code**.

[PAUSE: 1s]

[TONE: historical, sweeping]
For *fifty years*, generating new code was expensive. Writing from scratch took hours, days, *weeks*. So when something broke, you patched. [PAUSE: 0.3s] Of *course* you patched. [PAUSE: 0.3s] It was rational.

[PAUSE: 1.5s]

[TONE: significant, emphatic]
[PACE: slightly slower]
But look where we are **now**. The cost to generate code just crossed **below** the cost to carefully patch it.

[PAUSE: 2s]

[TONE: appreciative but pivoting]
Tools like Cursor and Claude Code are *fantastic*. Best darning needles **ever made**. They make patching faster, cleaner, less painful.

[PAUSE: 1s]

[TONE: pointed, landing the blow]
But they're still **darning needles**.

[PAUSE: 1.5s]

[TONE: weary wisdom]
And here's the thing about darning: every patch you add makes the *next* patch harder. The sock gets stiffer. The code gets more tangled. Patches... [PAUSE: 0.5s] **accumulate**.

[PAUSE: 1.5s]

[TONE: revealing a secret]
[PACE: slightly slower for emphasis]
This is the part of software economics *nobody talks about*. **Eighty to ninety percent** of software cost isn't building the initial system.

[PAUSE: 1s]

[TONE: driving home the point]
It's *maintaining* it. [PAUSE: 0.3s] Patching it. [PAUSE: 0.3s] Navigating around all the previous patches.

[PAUSE: 0.8s]

[EMOTION: ominous]
And those costs... **compound**.

---

## PART 2: THE PARADIGM SHIFT (5:00 - 8:00)

[PAUSE: 2s]

[TONE: curious, investigative]
So what *actually* changed with clothes? It wasn't just that fabric got cheaper.

[PAUSE: 1s]

[TONE: revelatory]
It was a **paradigm shift** in manufacturing. From crafting individual objects... [PAUSE: 0.5s] to designing **molds**.

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

[TONE: grand reveal]
[PACE: slightly slower]
**This** is Prompt-Driven Development.

[PAUSE: 1.5s]

[TONE: crystallizing the metaphor]
The prompt is your mold. The code is just... *plastic*.

---

## PART 3: THE MOLD HAS THREE PARTS (8:00 - 13:00)

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

[PAUSE: 0.8s]

When the model generates code, it *sees* these tests. The code it produces must pass them. It literally **cannot** generate code that violates these walls.

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
A good prompt is *much smaller* than the code it generates. You're specifying *what* and *why*... not *how*.

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

[PAUSE: 1.5s]

[TONE: emphatic, memorable]
The code is *output*. The mold is what **matters**.

---

## PART 4: THE PRECISION TRADEOFF (13:00 - 15:00)

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
More tests, less prompt. The walls do the precision work.

---

## PART 5: COMPOUND RETURNS (15:00 - 17:00)

[PAUSE: 2s]

[TONE: strategic, analytical]
Let's talk about **compound returns**.

[PAUSE: 1s]

[TONE: describing the old way]
When you patch code, each fix has *local* returns. You fixed one bug in one place. Similar bugs can still occur elsewhere. And sometimes your patch introduces *new* bugs.

[PAUSE: 0.8s]

[TONE: dismissive]
The returns are linear at best. Often *sub*linear.

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

---

## PART 6: THE SKILL SHIFT (17:00 - 18:30)

[PAUSE: 2s]

[TONE: addressing concerns, reassuring]
One more thing. This transition doesn't eliminate developers. It **elevates** them.

[PAUSE: 1.5s]

[TONE: insightful]
Mold designers need *deeper* understanding than woodcarvers. They need to understand materials, physics, tolerances, failure modes.

[PAUSE: 1s]

[TONE: empowering]
PDD developers work at the level of *specification*. You're not writing the defensive code—you're specifying what defensive behavior **looks like**. You're not implementing the error handling—you're defining the *contract* it must satisfy.

[PAUSE: 1.5s]

[TONE: crystallizing]
The shift: from *implementation* craft... to **specification** craft.

[PAUSE: 1s]

[TONE: honest, grounded]
The code is still there. It's still complex. But you don't *live* in it anymore. You live in the **specification**. The code is generated, verified, and—if needed—*regenerated*.

---

## CLOSING (18:30 - 20:00)

[PAUSE: 2s]

[TONE: wrapping up, reflective]
[PACE: measured, deliberate]
So here's the mental shift.

[PAUSE: 1.5s]

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

**Total runtime: ~18-20 minutes**
