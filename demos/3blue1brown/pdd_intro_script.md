# Prompt-Driven Development: A 3Blue1Brown Style Video Script

**Working Title:** "Why You're Still Darning Socks"
**Duration:** ~19-21 minutes
**Visual Style:** Manim animations, clean geometric representations, smooth transitions

---

## COLD OPEN: THE SOCK HOOK (0:00 - 2:00)

**[VISUAL: Split screen. LEFT: Developer at keyboard, Cursor interface visible, making a slick AI-assisted edit. RIGHT: 1950s grandmother carefully darning a wool sock by lamplight.]**

**NARRATOR:**
If you use Cursor, or Claude Code, or Copilot...

**[VISUAL: Both complete their task simultaneously. The code edit lands cleanly. The sock patch finishes neatly.]**

...you're getting really good at this.

**[VISUAL: Zoom out on the LEFT: The single edit is revealed to be one of thousands of patches in a massive codebase. Files everywhere, diff markers, TODO comments. Zoom out on the RIGHT: Grandmother's drawer opens—dozens of carefully mended socks, shirts, trousers.]**

**[VISUAL: Split screen holds. Both sides show the accumulated weight of all that careful repair work.]**

But here's what your great-grandmother figured out sixty years ago.

**[VISUAL: Hard cut to modern day. A person notices a hole in their sock. They shrug, toss it in the trash, and grab a fresh pair from a multi-pack.]**

When socks got cheap enough... she stopped.

**[VISUAL: Return to the code side. The cursor blinks on a complex function full of patches. Hold for a beat.]**

Code just got that cheap.

**[VISUAL: The entire function DELETES. Then regenerates, clean, in under a second. In the corner, subtle: terminal showing `pdd generate` completing.]**

So why are we still patching?

**[VISUAL: Title card fades in over the regenerated code: "Prompt-Driven Development"]**

---

## PART 1: THE ECONOMICS OF DARNING (2:00 - 5:45)

**[VISUAL: Price chart animation. 1950: A pair of quality wool socks costs about an hour of wages. Graph shows labor cost vs garment cost over time. The lines cross around 1970-80.]**

**NARRATOR:**
This isn't nostalgia. It's economics.

**[VISUAL: The crossing point highlights. Label: "The Threshold"]**

In 1950, a wool sock cost real money relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar.

**[VISUAL: The lines diverge dramatically. By 2020, socks are essentially free relative to labor.]**

By 1990, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational.

**[VISUAL: Transition to a similar chart for code. Y-axis: "Cost (Developer Hours)". Three elements: "Cost to generate" (blue line, high), "Immediate patch cost" (amber solid line, low), and a dashed amber line at the top labeled "Total cost (with debt)" with shaded area between the two amber lines.]**

Now look at code.

**[VISUAL: Key dates appear on the falling "generate" line: GPT-3, Codex, GPT-4, Claude, Gemini. Each one drops the line further.]**

For fifty years, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational.

**[VISUAL: Post-2020, both the blue "generate" line AND the amber "immediate patch" line start dropping. The drops are real and visible—AI helps both.]**

Now, here's where it gets interesting. AI made patching faster too. Cursor, Claude Code, Copilot—they're incredible tools. They understand your codebase, suggest fixes, catch bugs before you make them.

**[VISUAL: Focus on the immediate patch line dropping. This is the viewer's lived experience. Validate it.]**

Look—each patch is getting faster. That's real. That's what you feel when you use these tools.

**[VISUAL: Camera pulls back. As the immediate line drops, the shaded debt area EXPANDS upward. The dashed "total cost" line at the top barely moves. The gap between what you feel and what's real becomes visible.]**

But watch the dashed line. The total cost. It's barely moving.

Because even though each patch is faster, every patch still leaves residue. Technical debt. And that debt accumulates—faster now, because you're patching faster.

**[VISUAL: Annotation appears: "Immediate: -60%" pointing to the dropping solid line. Another annotation: "Total: -4%" pointing to the nearly-flat dashed line. The contrast is stark.]**

AI gave you a sixty percent speedup on individual patches. But your total cost? Down four percent. The debt ate the rest.

**[VISUAL: Zoom into the shaded debt area. It separates into two distinct layers: a darker "Code Complexity" layer and a lighter "Context Rot" layer with a subtle static/noise texture.]**

And there's something else hiding in that debt. Something specific to AI-assisted development.

**[VISUAL: The chart morphs into a new visualization. A glowing rectangular "context window" appears over a small codebase represented as a 4x4 grid of code blocks. The window covers most of the grid (~80%).]**

When your codebase is small, AI tools are brilliant. The context window—what the model can actually see—covers almost everything. It understands how the pieces connect.

**[VISUAL: The codebase grid grows: 4x4 → 8x8 → 16x16 → 32x32. The context window stays the SAME SIZE. A counter shows: "Context coverage: 80% → 40% → 10% → 2%". The window becomes a tiny rectangle over a massive grid.]**

But codebases grow. And that window? It stays the same size.

**[VISUAL: Inside the tiny window, some blocks are highlighted red—irrelevant code that the AI grabbed. Outside the window, green-highlighted blocks show the code that was actually needed but couldn't be seen.]**

Now the AI is looking through a keyhole. It has to guess what's relevant. And increasingly, it guesses wrong. The code it needs is outside the window. The code inside? Something else entirely.

**[VISUAL: Return to the chart. The "Context Rot" layer in the debt area pulses. Annotation: "Faster patching → faster growth → faster rot".]**

This is why AI-assisted patching feels great at first and frustrating later. It's not the model getting dumber. It's the ratio getting worse. Every patch makes the codebase bigger. Every patch shrinks what the AI can see.

**[VISUAL: The "Generate" line pulses with emphasis. Small annotation: "Small modules. Clear prompts. Always fits in context."]**

Regeneration doesn't have this problem. A single module with a clear prompt? That fits in the window. Every time.

**[VISUAL: The blue "generate" line crosses below the dashed "total cost" line. Then keeps going, crossing below even the solid "immediate" line. Label: "We are here."]**

Meanwhile, generation just crossed below both lines. And it comes with no debt. No rot.

**[VISUAL: Split screen. Developer with Cursor / Grandma with needle. Both are working efficiently—this isn't dismissive of their tools.]**

Tools like Cursor and Claude Code are the best darning needles ever made. I use them. They're fantastic.

**[VISUAL: Zoom out on the developer's side. The codebase is massive, tangled. Comments appear: "// don't touch this", "// legacy", "// temporary fix (2019)"]**

But they're still darning needles. And the fundamental problem with darning isn't speed—it's accumulation.

**[VISUAL: Time-lapse of the codebase. Even with AI-assisted patches, complexity grows. Faster patching just means faster accumulation.]**

This is the part of software economics nobody talks about. 80 to 90 percent of software cost isn't building the initial system.

**[VISUAL: Pie chart materializes. "Initial Development: 10-20%". "Maintenance: 80-90%".]**

It's maintaining it. Navigating around all the previous patches. Understanding what the last ten developers did and why.

**[VISUAL: The pie chart morphs into an exponentially growing cost curve. A second, flat line appears: "Regeneration cost (no debt)".]**

And those costs compound. Unless you regenerate. Then they reset to zero.

---

## PART 2: THE PARADIGM SHIFT (5:45 - 8:45)

**[VISUAL: A factory floor. Industrial. An injection molding machine dominates the frame.]**

**NARRATOR:**
So what actually changed with clothes? It wasn't just that fabric got cheaper.

**[VISUAL: Close-up on the injection molding machine. Liquid plastic flows into a mold. The mold is precise—hard walls defining an exact shape.]**

It was a paradigm shift in manufacturing. From crafting individual objects... to designing molds.

**[VISUAL: The mold opens. A perfect plastic part ejects. Then another. Then another. Counter: 1... 10... 100... 10,000...]**

Make the mold once, produce unlimited identical parts. Refine the mold once, every future part improves automatically.

**[VISUAL: A defect appears in a molded part. Zoom in on the flaw.]**

And when there's a defect?

**[VISUAL: Instead of someone patching the individual part, the scene shifts to an engineer adjusting the mold itself. Subtle change to the mold wall.]**

You don't patch individual parts. You fix the mold. And that fix applies to every part you'll ever make again.

**[VISUAL: New parts eject. All perfect. The defective part is simply discarded.]**

**[VISUAL: Split screen. LEFT: A craftsman hand-carving a wooden chair. Each cut permanent, history accumulating in the wood. RIGHT: The injection mold with plastic flowing through it.]**

This is the real shift. Not "cheaper material." A migration of where value lives.

**[VISUAL: Glowing aura effect. On the LEFT, the aura surrounds the wooden chair—the object itself. On the RIGHT, the aura surrounds the MOLD, not the plastic part.]**

In crafting, value lives in the object. You protect the object. Losing the chair is losing everything.

In molding, value lives in the specification—the mold. The plastic part? Disposable. Regenerate it at will.

**[VISUAL: The plastic part dissolves. A new one instantly appears, identical.]**

**[VISUAL: Transition. The injection mold morphs into a glowing document labeled "PROMPT". The plastic part morphs into lines of code.]**

This is Prompt-Driven Development.

**[VISUAL: The prompt document pulses. Code flows out of it, filling a defined shape. Tests appear as walls around the code, constraining it.]**

The prompt is your mold. The code is just plastic.

---

## PART 3: THE MOLD HAS THREE PARTS (8:45 - 13:45)

**[VISUAL: Cross-section of an injection mold. Technical, precise. Three regions highlight one by one.]**

**NARRATOR:**
Now let's get precise. Because "prompt is the mold" is a nice metaphor, but it's incomplete.

In PDD, the mold has three components. Three types of capital you're accumulating.

### TEST CAPITAL: THE WALLS

**[VISUAL: The walls of the mold illuminate. Each wall segment gets a label: "null → None", "empty string → ''", "handles unicode", "latency < 100ms".]**

First: tests. Tests are the walls of your mold.

**[VISUAL: Animate liquid (representing code generation) being injected into the mold. It flows freely until it hits a wall, then stops. The shape is constrained by the walls.]**

Each test is a constraint. A boundary the generated code cannot cross.

**[VISUAL: Focus on one wall labeled "null → None". The liquid tries to flow past it, hits the wall, stops. The wall holds firm.]**

When the model generates code, it sees these tests. The code it produces must pass them. It literally cannot generate code that violates these walls.

**[VISUAL: A bug is discovered. Red alert on a piece of code. The word "BUG" appears.]**

Now here's where it gets interesting. When you find a bug...

**[VISUAL: Instead of patching the code, a new wall materializes in the mold. The wall is labeled with the bug condition. In the corner, subtle terminal: `pdd bug user_parser` running, outputting "Creating failing test..."]**

...you don't patch the code. You add a wall.

**[VISUAL: The mold now has one more wall. The code regenerates, automatically conforming to the new constraint. Terminal in corner shows: `pdd fix user_parser` → "All tests passing".]**

That wall is permanent. That bug can never occur again—not in this generation, not in any future generation.

**[VISUAL: Time-lapse. More bugs found, more walls added. The mold becomes more precise over time. But critically—walls only accumulate. None disappear. Subtle: `pdd test` output scrolling in corner, green checkmarks accumulating.]**

This is the ratchet effect. Tests only accumulate. The mold only gets more precise. Each wall you add constrains all future generations.

**[VISUAL: Split screen comparison:
LEFT: "Traditional" - Bug found → Patch code → Similar bug elsewhere → Patch again → Different bug → Patch again...
RIGHT: "PDD" - Bug found → Add test (`pdd bug`) → Regenerate (`pdd fix`) → Bug impossible forever]**

In traditional development, a bug fix helps one place. In PDD, a test prevents that bug everywhere, forever.

### PROMPT CAPITAL: THE SPECIFICATION

**[VISUAL: The injection nozzle of the mold highlights. Labels appear: "intent", "requirements", "constraints".]**

Second: the prompt. Your specification of what you want.

**[VISUAL: Text flows into the mold like injection material: "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode." A file briefly visible: `user_parser.prompt`]**

The prompt doesn't define the walls—tests do that. The prompt defines what you're asking for and why.

**[VISUAL: Show the same prompt generating code twice. The code is slightly different each time—different variable names, slightly different structure—but both versions pass all tests. Terminal: `pdd generate user_parser.prompt` runs twice, different outputs, both valid.]**

And here's something subtle: the exact implementation can vary. What's locked is the *behavior*. The code is flexible; the contract is fixed.

**[VISUAL: The prompt glows. It's small—maybe 10-15 lines. But it governs a 200-line code file.]**

A good prompt is much smaller than the code it generates. You're specifying *what* and *why*, not *how*.

### GROUNDING CAPITAL: THE MATERIAL

**[VISUAL: A panel showing material properties. "Grounding" label. Different textures/colors flow: one labeled "OOP", one "Functional", one "Your Team's Style".]**

Third: grounding. This determines the properties of what fills the mold.

**[VISUAL: Same prompt, same tests. But two different grounding contexts:
Path A: Grounding from OOP codebase → generates classes with methods
Path B: Grounding from functional codebase → generates pure functions with composition]**

Grounding is learned from your past generations. When you successfully generate and fix code, that knowledge feeds back into the system.

**[VISUAL: A successful generation glows, then flows into a "Grounding Database". Future generations pull from this database. Subtle: after `pdd fix` succeeds, an arrow shows the (prompt, code) pair flowing to cloud storage.]**

Your style. Your patterns. Your team's conventions. Grounding captures all of it and applies it automatically to future generations.

**[VISUAL: Pull back to see all three components working together. Prompt flows in → passes through grounding → fills the mold → constrained by test walls → code emerges.]**

Prompt plus tests plus grounding. Intent plus constraints plus style. Together, they form a complete specification.

**[VISUAL: The code that emerges is clean, consistent, correct. It glows briefly, then the glow fades—it's just output. The mold continues to glow.]**

The code is output. The mold is what matters.

---

## PART 4: THE PRECISION TRADEOFF (13:45 - 15:45)

**[VISUAL: Split screen. LEFT: A 3D printer depositing material precisely, layer by layer. RIGHT: Injection mold with liquid flowing until it hits walls.]**

**NARRATOR:**
Here's something subtle that changes how you think about prompts.

**[VISUAL: Focus on 3D printer. Highlight how every single point must be specified. A coordinate grid appears, showing the precision required.]**

In 3D printing, there's no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise.

**[VISUAL: Focus on injection mold. The liquid flows freely, chaotically even—until it hits walls. The walls do the precision work.]**

In injection molding, precision comes from the walls. The material just flows until it's constrained.

**[VISUAL: Graph appears. X-axis: "Number of Tests". Y-axis: "Required Prompt Precision". An inverse curve forms—as tests increase, required prompt precision decreases.]**

This maps directly to PDD.

**[VISUAL: Animate along the curve. At the left (few tests), the prompt must be very detailed. At the right (many tests), the prompt can be minimal.]**

With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation.

**[VISUAL: A long, detailed prompt appears. Dense with requirements. File: `parser_v1.prompt` - 50 lines.]**

With many tests, the prompt only needs to specify intent. The tests handle the constraints.

**[VISUAL: A short, minimal prompt appears. Just a few requirements. But it's surrounded by dozens of test walls. File: `parser_v2.prompt` - 10 lines. Terminal shows: `pdd test parser` with 47 tests passing.]**

**[VISUAL: The two scenarios generate code. Both produce correct output. But one required a 50-line prompt, the other a 10-line prompt.]**

This is why test accumulation matters. It's not just about catching bugs. It's about making prompts simpler and regeneration safer over time.

**[VISUAL: Text appears, emphasized: "More tests, less prompt. The walls do the precision work."]**

The more walls you have, the less you need to specify. The mold does the precision work.

---

## PART 5: COMPOUND RETURNS (15:45 - 17:45)

**[VISUAL: A graph with two curves. One labeled "Patching", one labeled "PDD". X-axis is time. Y-axis is "Cumulative Value of Investment".]**

**NARRATOR:**
Let's talk about compound returns.

**[VISUAL: The "Patching" curve. Each patch is a point of investment. The return is local—one bug fixed. The curve grows linearly, then starts to flatten as patches interact badly.]**

When you patch code, each fix has local returns. You fixed one bug in one place. Similar bugs can still occur elsewhere. And sometimes your patch introduces new bugs.

**[VISUAL: The patching curve wobbles, occasionally dips as patches conflict.]**

The returns are linear at best. Often sublinear.

**[VISUAL: The "PDD" curve. Each test added is a point of investment. The return compounds—that test constrains all future generations.]**

When you add a test in PDD, the returns are different.

**[VISUAL: The PDD curve grows exponentially. Each test contributes to every future generation. The gap between the curves widens dramatically.]**

That test you wrote today? It constrains tomorrow's generation. And next week's. And next year's. It's a permanent wall.

**[VISUAL: Investment table appears:

| Investment | Return (Patching) | Return (PDD) |
|------------|------------------|--------------|
| Fix bug | One place, once | Impossible forever |
| Improve code | One version | All future versions |
| Document behavior | One snapshot | Living specification |]**

Every investment in the mold has compound returns. Every investment in patching has diminishing returns.

**[VISUAL: Return to the 1950s grandmother and modern person with socks.]**

Your great-grandmother wasn't stupid for darning socks. The economics made it rational.

**[VISUAL: Return to the developer with Cursor.]**

And you're not stupid for patching code. Until now, the economics made it rational.

**[VISUAL: The economics chart from earlier. The crossing point pulses again.]**

But the economics changed. And when economics change, behavior that was rational becomes... darning socks.

---

## PART 6: THE SKILL SHIFT (17:45 - 19:15)

**[VISUAL: A craftsman looking at an injection molding machine, uncertain. Then sitting at a CAD workstation, designing molds. Their expression shifts from uncertainty to engagement.]**

**NARRATOR:**
One more thing. This transition doesn't eliminate developers. It elevates them.

**[VISUAL: Skill mapping animation:
- "Writing code" morphs into "Writing tests"
- "Debugging" morphs into "Specifying constraints"
- "Refactoring" morphs into "Refining prompts"
- "Reading legacy code" morphs into "Reading specifications"]**

Mold designers need deeper understanding than woodcarvers. They need to understand materials, physics, tolerances, failure modes.

**[VISUAL: A developer writing a test. Then refining a prompt. Reviewing generated code with a critical eye. Working at a higher level of abstraction.]**

PDD developers work at the level of specification. You're not writing the defensive code—you're specifying what defensive behavior looks like. You're not implementing the error handling—you're defining the contract it must satisfy.

**[VISUAL: Text appears: "From implementation craft → specification craft"]**

The shift: from implementation craft to specification craft.

**[VISUAL: Two developers side by side. One is deep in a complex codebase, tracing through patches. The other is looking at a clean prompt and a comprehensive test suite. Both are working hard, but the nature of the work is different.]**

The code is still there. It's still complex. But you don't live in it anymore. You live in the specification. The code is generated, verified, and—if needed—regenerated.

---

## CLOSING (19:15 - 20:45)

**[VISUAL: Pull back to show a complete system. Multiple modules, each with a prompt, tests, and generated code. The prompts and tests glow steadily. The code is present but not highlighted—it's output.]**

**NARRATOR:**
So here's the mental shift.

**[VISUAL: The sock metaphor returns one final time. A holey sock. A person considers it for a moment, then discards it and grabs a fresh one.]**

You don't patch socks because socks got cheap. The economics made patching irrational.

**[VISUAL: Code with a bug. A developer considers it. Instead of opening the file to patch, they add a test and hit "regenerate". Terminal visible: `pdd bug → pdd fix → ✓`]**

Code just got that cheap.

**[VISUAL: The three components appear as a triangle: PROMPT (top), TESTS (bottom left), GROUNDING (bottom right). Code appears in the center, generated from the three.]**

Prompts encode intent.
Tests preserve behavior.
Grounding maintains style.

**[VISUAL: The code in the center dissolves and regenerates. Dissolves and regenerates. Each time slightly different but always passing all tests, always satisfying the prompt. Subtle loop: `pdd generate` → code appears → `pdd test` → ✓ → repeat.]**

Code is generated, verified, and disposable.

**[VISUAL: Final frame. The mold glows. The plastic part is present but unremarkable.]**

The code is just plastic.

**[VISUAL: Beat.]**

The mold is what matters.

**[VISUAL: Fade to black. Title card: "Prompt-Driven Development" with URL. Below, subtle: `uv tool install pdd-cli`]**

---

## VISUAL DESIGN NOTES

### Color Palette
- **Prompts:** Cool blue (#4A90D9)
- **Tests/Walls:** Warm amber (#D9944A)
- **Grounding:** Soft green (#5AAA6E)
- **Generated Code:** Neutral gray, inherits slight blue tint
- **Patched Code:** Warmer gray, accumulates red tint as patches increase
- **Cursor/Claude Code UI:** Accurate to real products, slightly desaturated
- **Terminal/Commands:** Monospace, subtle gray background, not attention-grabbing

### Key Visual Motifs

1. **The Split Screen** - Sock darning / code patching parallel. Use at open, at economic crossing point, at close.

2. **The Mold Cross-Section** - Technical, precise. Walls clearly defined. Liquid flowing and being constrained.

3. **The Glow** - Indicates where value resides. Always on the specification (prompt + tests), never on the generated code.

4. **The Ratchet** - Mechanical ratchet animation when adding tests. Click-click-click. Walls only accumulate.

5. **The Compound Curves** - Mathematical, clean. Linear/sublinear for patching. Exponential for PDD.

6. **The Subtle Terminal** - Commands appear in corner/background, never center frame. They're discoverable, not advertised.

### PDD Commands Visual Placement

Commands appear as subtle terminal snippets in the corner or background. They should be:
- Readable if you're looking for them
- Not distracting from the main narrative
- Consistent in position (bottom-right corner recommended)
- Monospace font, muted colors

| Timestamp | Section | Command Shown |
|-----------|---------|---------------|
| 0:38 | Cold open regeneration | `pdd generate` |
| 9:45 | Bug discovered, add test | `pdd bug user_parser` |
| 10:02 | Regenerate after test | `pdd fix user_parser` |
| 10:30 | Test accumulation | `pdd test` (scrolling output) |
| 10:55 | Split screen comparison | `pdd bug` → `pdd fix` |
| 11:20 | Prompt file | `user_parser.prompt` visible |
| 11:45 | Generate variations | `pdd generate` (twice) |
| 12:30 | Grounding feedback | Arrow to cloud after `pdd fix` |
| 14:15 | Many tests | `pdd test parser` (47 passing) |
| 19:15 | Final workflow | `pdd bug → pdd fix → ✓` |
| 19:45 | End card | `uv tool install pdd-cli` |

### Animation Principles
- Smooth easing on all transitions (3B1B signature style)
- Code appears in blocks, not character-by-character (except for emphasis)
- Morphing transformations for paradigm shifts (sock→code, wood→plastic, craft→mold)
- Mathematical notation clean, appears with slight bounce
- Split screens use clean vertical divide, both sides animate in sync
- Terminal commands: fade in, hold, fade out. Never animated typing.

### Sound Design Notes
- Soft "flow" sound for generation (like water through channels)
- Solid "click" for test walls locking in place
- Discordant tones for patch accumulation
- Harmonious resolution when code regenerates clean
- Subtle "crumple" for sock being discarded
- Terminal commands: optional soft keystroke sound, very quiet

---

## POTENTIAL FOLLOW-UP VIDEOS

1. **"The Context Window Problem"** - Why agentic tools degrade over long sessions (15 min)
2. **"Tests as Specification, Not Verification"** - The TDD connection (12 min)
3. **"The Grounding Deep Dive"** - How few-shot learning creates consistency (10 min)
4. **"When to Patch vs Regenerate"** - Practical decision framework (8 min)
5. **"Building Your First Mold"** - Hands-on PDD tutorial (20 min)
