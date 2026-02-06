# Section 1.6: Context Rot - The AI-Specific Problem

**Tool:** Remotion
**Duration:** ~45 seconds
**Timestamp:** 3:43 - 4:41

## Visual Description

Zoom into the debt area of the chart and reveal it contains two compounding factors: traditional code complexity AND context rot (an AI-specific degradation). Visualize how the context window becomes a "keyhole" as codebases grow.

## Narrative Purpose

This section explains the mechanism behind the fork the viewer just saw in the code cost chart:
1. Connects to the fork ("You just saw patching split into two paths...")
2. Reveals WHY the large-codebase path stays flat ("...here's what's happening inside that debt area")
3. Validates the viewer's experience ("AI was great at first, but now it suggests weird things")
4. Sets up regeneration as the solution (small modules always fit in context)

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Same dark (#1a1a2e)
- Starts zoomed into the chart's debt area

### Part 1: Zoom Into the Debt (0-10s)

**Animation Sequence:**
1. **Frame 0-60 (0-2s):** Zoom into the shaded debt area above the **large-codebase** fork
   - The small-codebase fork and generate line fade to 20% opacity
   - The large-codebase path and its debt area expand to fill most of the frame
   - The fork point (2020) remains faintly visible at the left edge as an anchor
2. **Frame 60-150 (2-5s):** The debt area separates into two distinct layers
   - Bottom layer (darker amber): "Code Complexity" - traditional tech debt
   - Top layer (lighter amber with static/noise texture): "Context Rot"
   - Labels fade in for each layer
3. **Frame 150-300 (5-10s):** Hold, showing the two-layer composition

**Visual Style:**
- "Code Complexity" layer: Solid amber (#D9944A) at 40% opacity
- "Context Rot" layer: Lighter amber (#E8B888) with subtle animated noise/static texture
- The static texture suggests "signal degradation" or "interference"

### Part 2: The Shrinking Window (10-30s)

**New Visual:** Transition to a "context window" metaphor

**Frame 300-360 (10-12s):** Morph the chart into a new visualization
- A rectangular "window" (glowing blue border) appears over a codebase representation
- The codebase is shown as a grid of code blocks

**Frame 360-540 (12-18s):** "Small Codebase" state
- Codebase: Small grid (maybe 4x4 blocks)
- Context window: Covers most of it (80%+)
- Label: "Small project - AI sees almost everything"
- Inside window: Blocks are clear, readable
- Outside window: Slightly dimmed

**Frame 540-720 (18-24s):** Animate codebase growth
- Grid expands: 4x4 → 8x8 → 16x16 → 32x32
- Context window stays the SAME SIZE
- The ratio visually shrinks
- Counter in corner: "Context coverage: 80% → 40% → 10% → 2%"

**Frame 720-900 (24-30s):** "Large Codebase" state
- Codebase: Large grid filling the frame
- Context window: Tiny rectangle, covering ~2%
- Label: "Large project - AI sees through a keyhole"
- Inside window: Random snippets, some clearly irrelevant
- Visual: Wrong/irrelevant blocks highlighted in red briefly

### Part 3: The Consequence (30-45s)

**Frame 900-1020 (30-34s):** Show the degradation in action
- Split view: Left = what AI puts in context, Right = what's actually relevant
- Mismatch visualization: Some relevant code is OUTSIDE the window
- Some irrelevant code is INSIDE the window

**Frame 1020-1140 (34-38s):** Return to the chart
- Zoom back out to show full chart with the fork visible
- The large-codebase fork's "Context Rot" layer now pulses slightly
- The small-codebase fork glows faintly below — a reminder of what's possible at small scale
- Annotation: "Faster patching = faster growth = faster rot"

**Frame 1140-1350 (38-45s):** Setup for the solution
- The "Generate" line pulses
- Small annotation appears: "Regeneration: always starts small, always fits"
- Hold for transition to crossing point

## Visual Elements

### The Context Window
- Border: Glowing blue (#4A90D9) with subtle pulse
- Interior: Clear, full opacity
- Exterior: Dimmed, 40% opacity
- Size: Fixed throughout the growth animation (this is the key visual)

### The Codebase Grid
- Blocks: Rounded rectangles representing code files/modules
- Colors: Various grays and muted colors (like a code editor)
- Growth: Smooth expansion animation with easing
- Some blocks have small red dots (bugs) that multiply as grid grows

### The "Wrong Context" Visualization
- Relevant blocks: Soft green glow (#5AAA6E)
- Irrelevant blocks: No glow, slightly red-tinted
- Inside window: Mix of both (showing the problem)
- Visual should be immediately readable: "AI grabbed the wrong stuff"

## Narration Sync

> [Zoom into debt area above the large-codebase fork]
> "Remember that fork? On large codebases, patching didn't help. Let's look at why. There's something hiding in that debt area."

> [Debt separates into two layers]
> "Traditional complexity, yes. But also this—context rot. An AI-specific problem."

> [Context window appears over small codebase]
> "When your codebase is small, AI tools are brilliant. The context window—what the model can actually see—covers almost everything."

> [Codebase grows, window stays fixed]
> "But codebases grow. And that window? It stays the same size."

> [Large codebase with tiny window]
> "Now the AI is looking through a keyhole. It has to guess what's relevant. And increasingly, it guesses wrong."

> [Mismatch visualization]
> "The code it needs is outside the window. The code inside is... something else. And the patches it suggests? They're based on incomplete information."

> [Return to chart — fork visible]
> "This is why the fork exists. Small codebase? The window covers everything. Large codebase? The ratio gets worse with every patch. It's not the model getting dumber. It's the codebase outgrowing the window."

> [Generate line pulses]
> "Regeneration doesn't have this problem. A single module with a clear prompt? That always fits."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={1350}>
  {/* Part 1: Zoom into large-codebase debt area */}
  <Sequence from={0} durationInFrames={300}>
    <ZoomToDebtArea chart={<CodeCostChart />} target="large-codebase-fork" />
    <DebtLayerSeparation
      layer1={{ label: "Code Complexity", color: "#D9944A", opacity: 0.4 }}
      layer2={{ label: "Context Rot", color: "#E8B888", hasNoise: true }}
    />
  </Sequence>

  {/* Part 2: Context window metaphor */}
  <Sequence from={300} durationInFrames={600}>
    <ContextWindowVisualization>
      {/* Small codebase */}
      <Sequence from={0} durationInFrames={180}>
        <CodebaseGrid size={4} />
        <ContextWindow coverage={0.8} />
        <Label text="Small project - AI sees almost everything" />
      </Sequence>

      {/* Growth animation */}
      <Sequence from={180} durationInFrames={180}>
        <AnimatedCodebaseGrowth
          from={4}
          to={32}
          duration={180}
        />
        <ContextWindow coverage="shrinking" /> {/* Fixed size, shrinking ratio */}
        <CoverageCounter from={80} to={2} suffix="%" />
      </Sequence>

      {/* Large codebase */}
      <Sequence from={360} durationInFrames={180}>
        <CodebaseGrid size={32} />
        <ContextWindow coverage={0.02} />
        <Label text="Large project - AI sees through a keyhole" />
        <IrrelevantCodeHighlight /> {/* Red flashes on wrong blocks */}
      </Sequence>
    </ContextWindowVisualization>
  </Sequence>

  {/* Part 3: Consequence and return */}
  <Sequence from={900} durationInFrames={450}>
    {/* Mismatch visualization */}
    <Sequence from={0} durationInFrames={120}>
      <SplitView
        left={<ContextContents label="What AI sees" />}
        right={<RelevantCode label="What's actually needed" />}
      />
      <MismatchHighlight />
    </Sequence>

    {/* Return to chart — fork visible */}
    <Sequence from={120} durationInFrames={120}>
      <ZoomOutToChart showFork={true} />
      <PulsingLayer layer="contextRot" target="large-codebase-fork" />
      <GlowingLine line="small-codebase-fork" opacity={0.4} />
      <Annotation text="Faster patching = faster growth = faster rot" />
    </Sequence>

    {/* Setup solution */}
    <Sequence from={240} durationInFrames={210}>
      <PulsingLine line="generate" color="#4A90D9" />
      <Annotation
        text="Regeneration: always starts small, always fits"
        position="near-generate-line"
      />
    </Sequence>
  </Sequence>
</Sequence>
```

## Data Points

### Context Window vs Codebase Size

| Codebase Size | Context Window | Coverage | AI Accuracy |
|---------------|----------------|----------|-------------|
| 10K LOC | 100K tokens | ~80% | Excellent |
| 100K LOC | 100K tokens | ~20% | Good |
| 500K LOC | 100K tokens | ~5% | Degraded |
| 1M+ LOC | 100K tokens | ~2% | Poor |

### Visual Representation
- Context window size is fixed (representing ~100K tokens)
- Codebase grid squares represent ~10K LOC each
- The animation shows the grid growing while window stays constant

## Design Notes

### The Key Visual Insight
The context window staying the same size while the codebase grows is the "aha moment."
It should feel slightly uncomfortable—the viewer should viscerally feel the shrinking ratio.

### Texture for Context Rot
The "static/noise" texture on the context rot layer suggests:
- Signal degradation (like a bad TV signal)
- Uncertainty/randomness
- Something is being lost

This contrasts with the solid "code complexity" layer which is predictable and measurable.

### Sound Design Suggestions
- As codebase grows: Low rumble or building tension
- When ratio hits critical threshold: Subtle "warning" tone
- When returning to chart: Resolution/clarity sound
- "Regeneration" mention: Clean, clear tone

## Transition

Zoom back out fully to show the crossing point (Section 1.7, was 1.6).
The crossing point now has even more weight—we've explained WHY the total cost stays high.
