# Section 1.4: Code Cost Chart

**Tool:** Remotion
**Duration:** ~120 seconds
**Timestamp:** 2:58 - 5:33

## Visual Description

Transition from the sock chart to a parallel chart for code. Shows the historical cost of generating code vs. patching code, with the "generate" line steep and high until recently.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Same dark (#1a1a2e)
- Fresh chart, but similar visual language

### Transition Effect

The sock chart morphs into the code chart:
- Axes labels transform ("Hours of labor" → "Developer hours")
- Lines reshape to new data
- Title changes: "The Economics of Code"

### Chart Elements

- **X-axis:** Years (2015 - 2025)
- **Y-axis:** "Cost (Developer Hours)" (0 - 100 hours for a typical module)
- **Line 1 (Cost to Generate/Write from Scratch):**
  - Color: #4A90D9 (cool blue)
  - Starts high (~32 hours in 2015)
  - Stays high through 2022
  - Then drops dramatically 2023-2025
- **Line 2 (Immediate Cost to Patch) — FORKS at 2020:**
  - Color: #D9944A (warm amber), solid line
  - Relatively flat (~10 hours) through 2020
  - At 2020, **FORKS into two paths:**
    - **Small codebase path** (solid amber): drops dramatically to ~1.5 hrs by 2025
    - **Large codebase path** (amber, thinner/dimmer): stays flat at ~10-12 hrs — context rot negates gains
  - The fork IS the story: same tools, opposite outcomes depending on codebase size
  - An arrow curves from the small-codebase fork upward toward the large-codebase fork, labeled "Every patch adds code"
- **Shaded Area (Tech Debt Accumulation):**
  - Color: #D9944A with 30% opacity fill above large-codebase immediate line
  - Represents the hidden cost: each patch makes future patches harder
  - **KEY VISUAL:** This area GROWS as the large-codebase immediate cost stays flat while debt rises
- **Line 3 (Total Cost of Patching, Large Codebase) - THE NET EFFECT:**
  - Color: #D9944A, **dashed line** at TOP of shaded area
  - = Large codebase immediate cost + Accumulated debt
  - **This line RISES** from 25 hrs (2020) to 33 hrs (2025) — it gets WORSE
  - Label: "True cost (including debt)"
  - This is what the "generate" line crosses FAR below
  - **Visual punch:** The small-codebase fork drops, but the total for large codebases actually increases

### Animation Sequence

1. **Frame 0-540 (0-18s):** Morphing transition from sock chart
   - Old labels fade, new labels fade in
   - Lines reshape smoothly

2. **Frame 540-750 (18-25s):** New axes and title fully visible
   - Only "Generate" and "Immediate Patch" lines visible initially

3. **Frame 750-1500 (25-50s):** Chart draws 2015 → 2020
   - "Cost to Generate" stays high (blue, solid)
   - "Immediate Cost to Patch" stays low (amber, solid)
   - Tech debt shaded area gradually grows above patch line
   - Dashed "Total Cost" line appears at top of shaded area

4. **Frame 1500-2700 (50-90s):** 2020 → 2025 - THE KEY MOMENT
   - "Immediate Patch" line begins to drop, then **FORKS** into two paths:
     - **Small codebase** (solid amber): plunges to 1.5 hrs — AI helps enormously
     - **Large codebase** (thinner amber): stays flat at ~10-12 hrs — context rot negates gains
   - Annotation: "Same tools. Different codebase sizes."
   - Arrow from small fork curving up toward large fork: "Every patch adds code"
   - "Generate" line stays near 30 through 2022, then plunges at 2023 (GPT-4/Claude arrive)
   - **Tech debt area** fills above the large-codebase line (the real-world path)
   - **Total cost line RISES** from 25 to 33 hrs — large codebases get WORSE, not better

5. **Frame 2700-3240 (90-108s):** Emphasis beat
   - Highlight the two forked paths:
     - Small codebase fork: 1.5 hrs — "This is what you feel"
     - Large codebase total: 33 hrs — "This is where you actually are"
   - Annotation near small-codebase fork: "Small codebase: -55% (Peng et al., 2023)"
   - Annotation near large-codebase fork: "Large codebase: +19% slower (METR, 2025)"
   - Annotation near rising total line: "Bug rate: +41% (Uplevel, 2024)"

6. **Frame 3240-3600 (108-120s):** Crossing point
   - Generate line (3 hrs) is FAR below large-codebase total (33 hrs) — 11x cheaper
   - Generate line (3 hrs) is ABOVE small-codebase immediate (1.5 hrs) — patching wins if small
   - Annotation: "Patching wins... if you stay small. But patching makes you grow."
   - Label: "We are here."

### Typography

- Title: "The Economics of Code" (centered top)
- Y-axis: "Developer Hours"
- X-axis: 2015 and 2020 marked, then individual years for 2020-2025

### Data Narrative

The key insight is MORE NUANCED than "generation got cheap":

1. **Pre-AI era (2015-2020):** Generation was expensive, patching was cheap. Patching was rational.
2. **AI era — small codebases:** AI dramatically reduced patching cost (-85%). This is real and we validate it.
3. **AI era — large codebases:** Context rot negates AI gains. Experienced devs are 19% *slower* (METR, 2025). Patching cost stays flat or rises.
4. **The self-defeating cycle:** Patching grows the codebase, pushing you from the small-codebase path to the large-codebase path. The tool that helps you today makes itself less effective tomorrow.
5. **Generation fell for ALL codebase sizes:** AI generates small, focused modules that always fit in context. No debt, no rot, no degradation.

The crossing point isn't just "generate < patch." It's "patching is self-defeating at scale, while generation stays cheap regardless of what came before." This acknowledges that AI patching genuinely works on small codebases — but shows why you can't stay there.

### Easing

- Morph transition: `easeInOutCubic` over 540 frames
- Line drawing: `easeOutQuad`

## Narration Sync

> "Now look at code."
>
> "For decades, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational."
>
> [The immediate patch line starts dropping, then FORKS into two paths:]
> "Now, here's where it gets interesting. AI made patching faster too. Cursor, Claude Code, Copilot—they're incredible tools."
>
> [Camera follows the small-codebase fork dropping:]
> "On a small codebase, each patch is getting faster. Fifty-five percent faster. That's real. That's what you feel."
>
> [Camera shifts to the large-codebase fork staying flat:]
> "But on a large codebase—the kind you get after years of patching—experienced developers are actually nineteen percent slower with AI tools. The context window can't keep up."
>
> [Arrow curves from small fork up toward large fork: "Every patch adds code"]
> "And here's the catch: every patch makes the codebase bigger. So patching pushes you from the world where AI helps into the world where it doesn't."
>
> [Camera pulls back to show the rising total cost line:]
> "Watch the dashed line. The total cost. For large codebases, it's not flat—it's rising. The debt isn't just eating the gains. It's outpacing them."
>
> [Annotations appear — study citations near their respective forks:]
> "GitHub measured a fifty-five percent speedup on individual coding tasks. But when Uplevel tracked eight hundred developers over a year? No change in throughput—and forty-one percent more bugs."
>
> [Generate line crosses far below the large-codebase total:]
> "Meanwhile, generation crossed below both paths. And it comes with no debt. No rot."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={3600}>
  {/* Morph transition */}
  <Sequence from={0} durationInFrames={540}>
    <MorphTransition
      from={<SockChart />}
      to={<CodeChartAxes />}
    />
  </Sequence>

  {/* Chart content - historical period (2015-2020) */}
  <Sequence from={540}>
    <ChartTitle text="The Economics of Code" />

    {/* Generate line - stays high */}
    <AnimatedLine
      data={costToGenerateData.slice(0, 2)}
      color="#4A90D9"
      strokeStyle="solid"
      drawDuration={960}
      label="Cost to generate"
    />

    {/* Immediate patch cost - stays low (single line before fork) */}
    <AnimatedLine
      data={immediateCostToPatch_baseline}
      color="#D9944A"
      strokeStyle="solid"
      drawDuration={960}
      label="Immediate patch cost"
    />

    {/* Tech debt - shaded area between immediate and total */}
    <AnimatedArea
      bottomData={immediateCostToPatch_baseline}
      topData={totalCostToPatch_largeCodebase}
      color="#D9944A"
      opacity={0.3}
      drawDuration={960}
    />

    {/* Total cost (dashed) - at top of shaded area */}
    <AnimatedLine
      data={totalCostToPatch_largeCodebase.slice(0, 2)}
      color="#D9944A"
      strokeStyle="dashed"
      drawDuration={960}
      label="Total cost (with debt)"
    />
  </Sequence>

  {/* AI era (2020-2025) - the key visual moment */}
  <Sequence from={1500}>
    {/* Generate plunges */}
    <AnimatedLine
      data={costToGenerateData.slice(1)}
      color="#4A90D9"
      strokeStyle="solid"
      drawDuration={1200}
    />

    {/* Immediate patch FORKS into two paths */}
    <AnimatedForkingLine
      sharedEnd={immediateCostToPatch_baseline[1]}  // 2020: 10 hrs
      forkData={[
        {
          data: immediateCostToPatch_smallCodebase,
          color: "#D9944A",
          strokeStyle: "solid",
          strokeWidth: 3,
          label: "Small codebase",
        },
        {
          data: immediateCostToPatch_largeCodebase,
          color: "#D9944A",
          strokeStyle: "solid",
          strokeWidth: 1.5,
          opacity: 0.7,
          label: "Large codebase",
        },
      ]}
      drawDuration={1200}
    />

    {/* Arrow from small fork curving up to large fork */}
    <CurvedArrow
      from="small-codebase-2023"
      to="large-codebase-2023"
      label="Every patch adds code"
      fadeIn={60}
      delay={600}
    />

    {/* Debt area above large-codebase immediate line */}
    <AnimatedArea
      bottomData={immediateCostToPatch_largeCodebase}
      topData={totalCostToPatch_largeCodebase}
      color="#D9944A"
      opacity={0.3}
      drawDuration={1200}
      expandAnimation={true}
    />

    {/* Total cost RISES for large codebases */}
    <AnimatedLine
      data={totalCostToPatch_largeCodebase.slice(1)}
      color="#D9944A"
      strokeStyle="dashed"
      drawDuration={1200}
      label="Total cost (large codebase)"
    />
  </Sequence>

  {/* Emphasis: study citation annotations */}
  <Sequence from={2700}>
    <Annotation
      text="Small codebase: -55% (Peng et al., 2023)"
      position="near-small-codebase-fork"
      fadeIn={30}
    />
    <Annotation
      text="Large codebase: +19% slower (METR, 2025)"
      position="near-large-codebase-fork"
      fadeIn={30}
      delay={30}
    />
    <Annotation
      text="Bug rate: +41% (Uplevel, 2024)"
      position="near-debt-area"
      fadeIn={30}
      delay={60}
    />
  </Sequence>

  {/* Crossing point */}
  <Sequence from={3240}>
    <CrossingPointHighlight
      generateValue={3}
      totalPatchValue_large={33}
      immediatePatchValue_small={1.5}
      immediatePatchValue_large={12}
      label="We are here."
      subLabel="Patching wins if you stay small. But patching makes you grow."
    />
  </Sequence>
</Sequence>
```

## Data Points (Approximate)

```json
{
  "costToGenerate": [
    { "year": 2015, "hours": 32 },
    { "year": 2020, "hours": 30 },
    { "year": 2022, "hours": 28 },
    { "year": 2023, "hours": 15 },
    { "year": 2024, "hours": 6 },
    { "year": 2025, "hours": 3 }
  ],
  "immediateCostToPatch_baseline (pre-fork)": [
    { "year": 2015, "hours": 10 },
    { "year": 2020, "hours": 10 }
  ],
  "immediateCostToPatch_smallCodebase (post-2020 fork)": [
    { "year": 2020, "hours": 10 },
    { "year": 2022, "hours": 5 },
    { "year": 2023, "hours": 3 },
    { "year": 2024, "hours": 2 },
    { "year": 2025, "hours": 1.5 }
  ],
  "immediateCostToPatch_largeCodebase (post-2020 fork)": [
    { "year": 2020, "hours": 10 },
    { "year": 2022, "hours": 10 },
    { "year": 2023, "hours": 11 },
    { "year": 2024, "hours": 12 },
    { "year": 2025, "hours": 12 }
  ],
  "techDebtAccumulation": [
    { "year": 2015, "hours": 12 },
    { "year": 2020, "hours": 15 },
    { "year": 2022, "hours": 17 },
    { "year": 2023, "hours": 19 },
    { "year": 2024, "hours": 20 },
    { "year": 2025, "hours": 21 }
  ],
  "totalCostToPatch_largeCodebase (computed: immediate_large + debt)": [
    { "year": 2015, "hours": 22, "note": "10 + 12" },
    { "year": 2020, "hours": 25, "note": "10 + 15" },
    { "year": 2022, "hours": 27, "note": "10 + 17" },
    { "year": 2023, "hours": 30, "note": "11 + 19" },
    { "year": 2024, "hours": 32, "note": "12 + 20" },
    { "year": 2025, "hours": 33, "note": "12 + 21" }
  ]
}
```

### The Visual Punch Line

| Year | Small CB Immediate | Large CB Immediate | Debt | **Large CB Total** | Generate |
|------|-------------------|-------------------|------|-------------------|----------|
| 2020 | 10 hrs | 10 hrs | +15 | **25 hrs** | 30 hrs |
| 2022 | 5 hrs (-50%) | 10 hrs (0%) | +17 | **27 hrs** | 28 hrs |
| 2023 | 3 hrs (-70%) | 11 hrs (+10%) | +19 | **30 hrs** | 15 hrs |
| 2024 | 2 hrs (-80%) | 12 hrs (+20%) | +20 | **32 hrs** | 6 hrs |
| 2025 | 1.5 hrs (-85%) | 12 hrs (+20%) | +21 | **33 hrs** | 3 hrs |

**The insight:** A tale of two codebases. On small codebases, AI-assisted patching dropped
immediate cost 85% (10→1.5 hrs) — genuinely transformative. But on large codebases, immediate
cost actually *rose* 20% (10→12 hrs) as context rot negated AI gains. And the total cost for
large codebases rose from 25 to 33 hrs — the debt didn't just eat the gains, it outpaced them.

Meanwhile, generation dropped 90% (30→3) with no debt. For large codebases, generation is
11x cheaper than the true cost of patching (3 vs 33 hrs). For small codebases, patching is
still competitive (1.5 vs 3 hrs) — but every patch makes the codebase bigger, pushing you
toward the large-codebase path. Only regeneration keeps modules permanently small.

### Key Visual Technique: The Fork

The most important moment in this animation is when the viewer sees the immediate patch
cost line FORK into two diverging paths:

1. **The small-codebase fork dropping** (bright amber, solid)
   - This matches their lived experience: "AI makes patching faster!"
   - We validate this completely. It IS faster. On small codebases.

2. **The large-codebase fork staying flat / rising** (dimmer amber, thinner)
   - This is the first surprise: "Wait—same tools, opposite outcome?"
   - The context window can't cover a large codebase. AI guesses wrong.

3. **The arrow between forks** ("Every patch adds code")
   - This is the "aha" moment: patching is self-defeating
   - Each patch grows the codebase, pushing you from the small path to the large path
   - The tool that helps you today makes itself less effective tomorrow

4. **The total cost line RISING** (amber dashed line goes UP)
   - For large codebases, debt doesn't just eat the gains—it outpaces them
   - Total cost rises from 25 to 33 hrs while generation drops to 3 hrs

**Animation note:** The fork should be visually dramatic—the two paths diverging like a
road splitting. The arrow between them should appear with a slight delay, creating
a "wait, you can't stay on the good path" moment. Consider having the small-codebase
fork pulse briefly (the dream) before the arrow appears (the reality).

### Data Sources & Rationale

**Historical (2015-2020):** Based on industry estimation benchmarks showing typical modules
at 30-40 hours. Gradual decline reflects improved languages, IDEs, and frameworks.

**AI Era (2020-2024):** Studies show 20-55% productivity gains for BOTH generation and patching:
- Peng et al. 2023: 55.8% faster task completion
- Microsoft/MIT RCT 2024: 26% more PRs/week
- Google Internal RCT: 21% faster

**Why AI patching diverges by codebase size:**
- Small codebases: AI context window covers most of the code, suggestions are accurate
- Large codebases: Context rot (Hong et al., 2025) — model performance degrades as input grows
- METR RCT 2025: Experienced devs 19% *slower* with AI on their own mature repos
- Hatton (1997): Modules of 200-400 LOC have lowest defect density — PDD's natural range

**Why generation falls faster than patching:**
- Generation benefits more from AI (full context, clean slate)
- Patching requires understanding existing code, which AI helps with but doesn't eliminate
- Studies show AI helps more with greenfield tasks than maintenance tasks

**Tech Debt Accumulation:** Based on the well-documented observation that 80-90% of software
costs are maintenance (Brooks, Jones, etc.). Maintenance costs scale exponentially with
codebase size (Banker, Datar, Kemerer & Zweig, 1993). Each patch adds complexity that
compounds. Regeneration resets this to zero—that's the key economic insight.

**The self-defeating cycle:** Every AI-assisted patch grows the codebase, degrading the AI's
effectiveness on the next patch. Patching pushes developers from the small-codebase path
(where AI helps) to the large-codebase path (where it doesn't). Only regeneration of small,
focused modules avoids this trajectory.

## Transition

Continues directly into Section 1.5 (AI milestones on the falling line).
