# Section 1.4: Code Cost Chart

**Tool:** Remotion
**Duration:** ~20 seconds
**Timestamp:** 2:45 - 3:05

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

- **X-axis:** Years (1970 - 2024)
- **Y-axis:** "Cost (Developer Hours)" (0 - 100 hours for a typical module)
- **Line 1 (Cost to Generate/Write from Scratch):**
  - Color: #4A90D9 (cool blue)
  - Starts very high (~80 hours in 1970)
  - Stays high through 2020
  - Then drops dramatically 2020-2024
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

1. **Frame 0-90 (0-3s):** Morphing transition from sock chart
   - Old labels fade, new labels fade in
   - Lines reshape smoothly

2. **Frame 90-150 (3-5s):** New axes and title fully visible
   - Only "Generate" and "Immediate Patch" lines visible initially

3. **Frame 150-360 (5-12s):** Chart draws 1970 → 2020
   - "Cost to Generate" stays high (blue, solid)
   - "Immediate Cost to Patch" stays low (amber, solid)
   - Tech debt shaded area gradually grows above patch line
   - Dashed "Total Cost" line appears at top of shaded area

4. **Frame 360-480 (12-16s):** 2020 → 2024 - THE KEY MOMENT
   - "Generate" line drops steeply (blue plunges down)
   - "Immediate Patch" line ALSO drops (amber goes down—validating AI tools)
   - **BUT:** Tech debt area EXPANDS upward as immediate line drops
   - **NET EFFECT:** The dashed "Total Cost" line barely moves
   - Visual: immediate cost and debt area move in opposite directions, canceling out

5. **Frame 480-540 (16-18s):** Emphasis beat
   - Highlight the gap between:
     - Where you FEEL you are (immediate cost: 4 hours)
     - Where you ACTUALLY are (total cost: 24 hours)
   - Annotation appears: "AI made each patch faster..."
   - Second annotation: "...but debt still accumulates"

6. **Frame 540-600 (18-20s):** Crossing point
   - Generate line (6 hrs) now FAR below total patch cost (24 hrs)
   - Generate line crosses below immediate patch cost too (4 hrs)
   - Label: "Generation: no accumulated debt"

### Typography

- Title: "The Economics of Code" (centered top)
- Y-axis: "Developer Hours"
- X-axis: Decades marked, then individual years for 2020-2024

### Data Narrative

The key insight is MORE NUANCED than "generation got cheap":

1. **Pre-AI era (1970-2020):** Generation was expensive, patching was cheap. Patching was rational.
2. **AI era (2020-2024):** AI reduced BOTH costs. Cursor, Claude Code, Copilot all make patching faster too.
3. **But generation fell faster:** The same AI that helps you patch can generate entire modules.
4. **The hidden cost:** Patching accumulates tech debt. Each patch makes the next one harder. Generation starts fresh—no debt.

The crossing point isn't just "generate < patch." It's "generate < patch + accumulated debt." This is a stronger, more honest argument that acknowledges AI-assisted patching while showing why regeneration wins.

### Easing

- Morph transition: `easeInOutCubic` over 90 frames
- Line drawing: `easeOutQuad`

## Narration Sync

> "Now look at code."
>
> "For fifty years, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational."
>
> [As both lines drop post-2020:]
> "And yes—AI made patching faster too. Cursor, Claude Code, Copilot—they're remarkable tools."
>
> [Camera follows the dropping immediate patch line:]
> "Look—the cost of each patch is falling. That's real. That's what you feel when you use these tools."
>
> [Camera pulls back to show the expanding debt area:]
> "But watch the total. Watch what happens to the dashed line."
>
> [Dashed line stays flat while immediate line drops:]
> "It's barely moving. Because every patch—even fast ones—still leaves residue. Technical debt."
>
> [Annotations appear:]
> "AI made each patch faster. But faster patches just means faster accumulation."
>
> [Generate line crosses far below total:]
> "Generation doesn't have this problem. You start fresh. No debt to inherit, no debt to leave behind."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={600}>
  {/* Morph transition */}
  <Sequence from={0} durationInFrames={90}>
    <MorphTransition
      from={<SockChart />}
      to={<CodeChartAxes />}
    />
  </Sequence>

  {/* Chart content - historical period (1970-2020) */}
  <Sequence from={90}>
    <ChartTitle text="The Economics of Code" />

    {/* Generate line - stays high */}
    <AnimatedLine
      data={costToGenerateData.slice(0, 6)}
      color="#4A90D9"
      strokeStyle="solid"
      drawDuration={270}
      label="Cost to generate"
    />

    {/* Immediate patch cost - stays low */}
    <AnimatedLine
      data={immediateCostToPatch.slice(0, 4)}
      color="#D9944A"
      strokeStyle="solid"
      drawDuration={270}
      label="Immediate patch cost"
    />

    {/* Tech debt - shaded area between immediate and total */}
    <AnimatedArea
      bottomData={immediateCostToPatch}
      topData={totalCostToPatch}
      color="#D9944A"
      opacity={0.3}
      drawDuration={270}
    />

    {/* Total cost (dashed) - at top of shaded area */}
    <AnimatedLine
      data={totalCostToPatch.slice(0, 4)}
      color="#D9944A"
      strokeStyle="dashed"
      drawDuration={270}
      label="Total cost (with debt)"
    />
  </Sequence>

  {/* AI era (2020-2024) - the key visual moment */}
  <Sequence from={360}>
    {/* Generate plunges */}
    <AnimatedLine
      data={costToGenerateData.slice(5)}
      color="#4A90D9"
      strokeStyle="solid"
      drawDuration={120}
    />

    {/* Immediate patch drops (AI helps!) */}
    <AnimatedLine
      data={immediateCostToPatch.slice(3)}
      color="#D9944A"
      strokeStyle="solid"
      drawDuration={120}
    />

    {/* Debt area EXPANDS as immediate drops */}
    <AnimatedArea
      bottomData={immediateCostToPatchRecent}
      topData={totalCostToPatchRecent}
      color="#D9944A"
      opacity={0.3}
      drawDuration={120}
      expandAnimation={true}  // Visually emphasize growth
    />

    {/* Total cost barely moves (the punch line) */}
    <AnimatedLine
      data={totalCostToPatch.slice(3)}
      color="#D9944A"
      strokeStyle="dashed"
      drawDuration={120}
    />
  </Sequence>

  {/* Emphasis: the gap between feeling and reality */}
  <Sequence from={480}>
    <Annotation
      text="AI made each patch faster..."
      position="near-immediate-line"
      fadeIn={30}
    />
    <Annotation
      text="...but debt still accumulates"
      position="near-total-line"
      fadeIn={30}
      delay={30}
    />
  </Sequence>

  {/* Crossing point */}
  <Sequence from={540}>
    <CrossingPointHighlight
      generateValue={6}
      totalPatchValue={24}
      label="Generation: no accumulated debt"
    />
  </Sequence>
</Sequence>
```

## Data Points (Approximate)

```json
{
  "costToGenerate": [
    { "year": 1970, "hours": 80 },
    { "year": 1980, "hours": 60 },
    { "year": 1990, "hours": 50 },
    { "year": 2000, "hours": 40 },
    { "year": 2010, "hours": 35 },
    { "year": 2020, "hours": 30 },
    { "year": 2022, "hours": 18 },
    { "year": 2023, "hours": 10 },
    { "year": 2024, "hours": 6 }
  ],
  "immediateCostToPatch": [
    { "year": 1970, "hours": 8 },
    { "year": 1990, "hours": 9 },
    { "year": 2010, "hours": 10 },
    { "year": 2020, "hours": 10 },
    { "year": 2022, "hours": 7 },
    { "year": 2023, "hours": 5 },
    { "year": 2024, "hours": 4 }
  ],
  "techDebtAccumulation": [
    { "year": 1970, "hours": 0 },
    { "year": 1990, "hours": 3 },
    { "year": 2010, "hours": 8 },
    { "year": 2020, "hours": 15 },
    { "year": 2022, "hours": 17 },
    { "year": 2023, "hours": 19 },
    { "year": 2024, "hours": 20 }
  ],
  "totalCostToPatch (computed: immediate + debt)": [
    { "year": 1970, "hours": 8,  "note": "8 + 0" },
    { "year": 1990, "hours": 12, "note": "9 + 3" },
    { "year": 2010, "hours": 18, "note": "10 + 8" },
    { "year": 2020, "hours": 25, "note": "10 + 15" },
    { "year": 2022, "hours": 24, "note": "7 + 17" },
    { "year": 2023, "hours": 24, "note": "5 + 19" },
    { "year": 2024, "hours": 24, "note": "4 + 20" }
  ]
}
```

### The Visual Punch Line

| Year | Immediate | Debt | **Total** | Generate |
|------|-----------|------|-----------|----------|
| 2020 | 10 hrs | +15 | **25 hrs** | 30 hrs |
| 2022 | 7 hrs (-30%) | +17 | **24 hrs** | 18 hrs |
| 2023 | 5 hrs (-50%) | +19 | **24 hrs** | 10 hrs |
| 2024 | 4.5 hrs (-55%) | +19.5 | **24 hrs** | 6 hrs |

**The insight:** Immediate patch cost dropped 55% (10→4.5), but total cost barely moved (25→24).
The debt ate all the productivity gains. Meanwhile, generation dropped 80% (30→6) with no debt.

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

**Historical (1970-2020):** Based on Fred Brooks' *Mythical Man-Month* (~10 LOC/day on
complex systems) and industry estimation benchmarks showing typical modules at 40-80 hours.
Gradual decline reflects improved languages, IDEs, and frameworks.

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
