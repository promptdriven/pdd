# Section 1.4: Code Cost Chart

**Tool:** Remotion
**Duration:** ~120 seconds
**Timestamp:** 2:45 - 4:45

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
- **Line 2 (Immediate Cost to Patch):**
  - Color: #D9944A (warm amber), solid line
  - Relatively flat (~8-10 hours) through 2020
  - ALSO drops 2020-2024 (AI helps patching too!)
  - Drops visibly—this validates the viewer's experience with AI tools
- **Shaded Area (Tech Debt Accumulation):**
  - Color: #D9944A with 30% opacity fill above Line 2
  - Represents the hidden cost: each patch makes future patches harder
  - **KEY VISUAL:** This area GROWS even as the immediate cost drops
  - The growth accelerates slightly post-2020 (faster patching = faster debt accumulation)
- **Line 3 (Total Cost of Patching) - THE NET EFFECT:**
  - Color: #D9944A, **dashed line** at TOP of shaded area
  - = Immediate cost + Accumulated debt
  - **This line stays nearly FLAT** even as immediate cost drops
  - Label: "True cost (including debt)"
  - This is what the "generate" line crosses BELOW
  - **Visual punch:** The immediate line drops, but the dashed total line barely moves

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
   - "Immediate Patch" line drops first (amber goes down—validating AI tools)
   - "Generate" line stays near 30 through 2022, then plunges at 2023 (GPT-4/Claude arrive)
   - **BUT:** Tech debt area EXPANDS upward as immediate line drops
   - **NET EFFECT:** The dashed "Total Cost" line barely moves
   - Visual: immediate cost and debt area move in opposite directions, canceling out

5. **Frame 2700-3240 (90-108s):** Emphasis beat
   - Highlight the gap between:
     - Where you FEEL you are (immediate cost: 4 hours)
     - Where you ACTUALLY are (total cost: 24 hours)
   - Annotation appears near dropping solid line: "Individual task: -55% (GitHub, 2022)"
   - Second annotation appears near flat dashed line: "Overall throughput: ~0% (Uplevel, 2024)"
   - Third annotation appears near expanding debt area: "Bug rate: +41% (Uplevel, 2024)"

6. **Frame 3240-3600 (108-120s):** Crossing point
   - Generate line (3 hrs) now FAR below total patch cost (24 hrs)
   - Generate line crosses below immediate patch cost too (4 hrs)
   - Label: "We are here."

### Typography

- Title: "The Economics of Code" (centered top)
- Y-axis: "Developer Hours"
- X-axis: 2015 and 2020 marked, then individual years for 2020-2025

### Data Narrative

The key insight is MORE NUANCED than "generation got cheap":

1. **Pre-AI era (2015-2020):** Generation was expensive, patching was cheap. Patching was rational.
2. **AI era (2020-2024):** AI reduced BOTH costs. Cursor, Claude Code, Copilot all make patching faster too.
3. **But generation fell faster:** The same AI that helps you patch can generate entire modules.
4. **The hidden cost:** Patching accumulates tech debt. Each patch makes the next one harder. Generation starts fresh—no debt.

The crossing point isn't just "generate < patch." It's "generate < patch + accumulated debt." This is a stronger, more honest argument that acknowledges AI-assisted patching while showing why regeneration wins.

### Easing

- Morph transition: `easeInOutCubic` over 540 frames
- Line drawing: `easeOutQuad`

## Narration Sync

> "Now look at code."
>
> "For decades, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational."
>
> [As both lines drop post-2020:]
> "Now, here's where it gets interesting. AI made patching faster too. Cursor, Claude Code, Copilot—they're incredible tools. They understand your codebase, suggest fixes, catch bugs before you make them."
>
> [Camera follows the dropping immediate patch line:]
> "Look—each patch is getting faster. That's real. That's what you feel when you use these tools."
>
> [Camera pulls back to show the expanding debt area:]
> "But watch the dashed line. The total cost. It's barely moving."
>
> "Because even though each patch is faster, every patch still leaves residue. Technical debt. And that debt accumulates—faster now, because you're patching faster."
>
> [Annotations appear — study citations near their respective lines:]
> "GitHub measured a fifty-five percent speedup on individual coding tasks. But when Uplevel tracked eight hundred developers over a year? No change in throughput—and forty-one percent more bugs. The debt ate the gains."
>
> [Generate line crosses far below both lines:]
> "Meanwhile, generation just crossed below both lines. And it comes with no debt. No rot."

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

    {/* Immediate patch cost - stays low */}
    <AnimatedLine
      data={immediateCostToPatch.slice(0, 2)}
      color="#D9944A"
      strokeStyle="solid"
      drawDuration={960}
      label="Immediate patch cost"
    />

    {/* Tech debt - shaded area between immediate and total */}
    <AnimatedArea
      bottomData={immediateCostToPatch}
      topData={totalCostToPatch}
      color="#D9944A"
      opacity={0.3}
      drawDuration={960}
    />

    {/* Total cost (dashed) - at top of shaded area */}
    <AnimatedLine
      data={totalCostToPatch.slice(0, 2)}
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

    {/* Immediate patch drops (AI helps!) */}
    <AnimatedLine
      data={immediateCostToPatch.slice(1)}
      color="#D9944A"
      strokeStyle="solid"
      drawDuration={1200}
    />

    {/* Debt area EXPANDS as immediate drops */}
    <AnimatedArea
      bottomData={immediateCostToPatchRecent}
      topData={totalCostToPatchRecent}
      color="#D9944A"
      opacity={0.3}
      drawDuration={1200}
      expandAnimation={true}  // Visually emphasize growth
    />

    {/* Total cost barely moves (the punch line) */}
    <AnimatedLine
      data={totalCostToPatch.slice(1)}
      color="#D9944A"
      strokeStyle="dashed"
      drawDuration={1200}
    />
  </Sequence>

  {/* Emphasis: study citation annotations */}
  <Sequence from={2700}>
    <Annotation
      text="Individual task: -55% (GitHub, 2022)"
      position="near-immediate-line"
      fadeIn={30}
    />
    <Annotation
      text="Overall throughput: ~0% (Uplevel, 2024)"
      position="near-total-line"
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
      totalPatchValue={24}
      immediatePatchValue={4}
      label="We are here."
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
  "immediateCostToPatch": [
    { "year": 2015, "hours": 10 },
    { "year": 2020, "hours": 10 },
    { "year": 2022, "hours": 7 },
    { "year": 2023, "hours": 5 },
    { "year": 2024, "hours": 4 },
    { "year": 2025, "hours": 3.5 }
  ],
  "techDebtAccumulation": [
    { "year": 2015, "hours": 12 },
    { "year": 2020, "hours": 15 },
    { "year": 2022, "hours": 17 },
    { "year": 2023, "hours": 19 },
    { "year": 2024, "hours": 20 },
    { "year": 2025, "hours": 21 }
  ],
  "totalCostToPatch (computed: immediate + debt)": [
    { "year": 2015, "hours": 22, "note": "10 + 12" },
    { "year": 2020, "hours": 25, "note": "10 + 15" },
    { "year": 2022, "hours": 24, "note": "7 + 17" },
    { "year": 2023, "hours": 24, "note": "5 + 19" },
    { "year": 2024, "hours": 24, "note": "4 + 20" },
    { "year": 2025, "hours": 24.5, "note": "3.5 + 21" }
  ]
}
```

### The Visual Punch Line

| Year | Immediate | Debt | **Total** | Generate |
|------|-----------|------|-----------|----------|
| 2020 | 10 hrs | +15 | **25 hrs** | 30 hrs |
| 2022 | 7 hrs (-30%) | +17 | **24 hrs** | 28 hrs |
| 2023 | 5 hrs (-50%) | +19 | **24 hrs** | 15 hrs |
| 2024 | 4 hrs (-60%) | +20 | **24 hrs** | 6 hrs |
| 2025 | 3.5 hrs (-65%) | +21 | **24.5 hrs** | 3 hrs |

**The insight:** Immediate patch cost dropped 65% (10→3.5), but total cost barely moved (25→24.5).
The debt ate all the productivity gains. Meanwhile, generation dropped 90% (30→3) with no debt.
By 2025, generation (3 hrs) crosses below even the immediate patch cost (3.5 hrs).

### Key Visual Technique: The Expanding Gap

The most important moment in this animation is when the viewer sees:

1. **The immediate line dropping** (amber solid line goes down)
   - This matches their lived experience: "AI makes patching faster!"
   - We validate this. We don't dismiss it.

2. **The debt area expanding** (amber shaded region grows upward)
   - As the immediate line drops, the gap between it and the total line GROWS
   - Visually: the shaded area expands to fill the space

3. **The total line staying flat** (amber dashed line barely moves)
   - This is the "aha" moment
   - "Wait—if patching got faster, why isn't the total dropping?"
   - Because debt accumulates. Faster patching = faster debt.

**Animation note:** Consider having the debt area "pulse" or glow slightly as it expands,
drawing attention to its growth. The total line should have subtle emphasis (glow, thicker
stroke) when it refuses to drop despite the immediate line falling.

### Data Sources & Rationale

**Historical (2015-2020):** Based on industry estimation benchmarks showing typical modules
at 30-40 hours. Gradual decline reflects improved languages, IDEs, and frameworks.

**AI Era (2020-2024):** Studies show 20-55% productivity gains for BOTH generation and patching:
- Peng et al. 2023: 55.8% faster task completion
- Microsoft/MIT RCT 2024: 26% more PRs/week
- Google Internal RCT: 21% faster

**Why generation falls faster than patching:**
- Generation benefits more from AI (full context, clean slate)
- Patching requires understanding existing code, which AI helps with but doesn't eliminate
- Studies show AI helps more with greenfield tasks than maintenance tasks

**Tech Debt Accumulation:** Based on the well-documented observation that 80-90% of software
costs are maintenance (Brooks, Jones, etc.). Each patch adds complexity that compounds.
Regeneration resets this to zero—that's the key economic insight.

## Transition

Continues directly into Section 1.5 (AI milestones on the falling line).
