[Remotion]

# Section 6.5: Regenerate & Compare Loop — Validating the Migration

**Tool:** Remotion
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 23:38 - 23:44

## Visual Description

A compact workflow diagram shows the cycle that validates a module's migration from code to specification. Four steps are arranged in a horizontal pipeline with curved arrows connecting them:

1. **Generate prompt** — A glowing `.prompt` document icon
2. **Add tests** — Amber wall icons accumulate beside the prompt
3. **Regenerate** — A terminal icon showing `pdd generate` with code flowing out
4. **Compare** — A split diff view showing original vs regenerated, both with green checkmarks

The pipeline animates left to right, each step lighting up in sequence. When the final "Compare" step completes with matching green checkmarks, a subtle loop arrow curves back from step 4 to step 2, suggesting the iterative nature: add more tests, regenerate, compare again. Each loop makes the specification more precise.

A progress bar below the pipeline fills as the steps complete. When the loop arrow appears, the bar resets to 80% and continues filling — each iteration gets closer to 100%.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Pipeline Steps (horizontal, centered at y: 420)
- Step spacing: 340px apart, starting at x: 200

##### Step 1: "Generate Prompt" at (200, 420)
- Icon: miniature document, 50×65px, `#4A90D9` at 0.4 border, `#0F172A` fill
- 4 horizontal lines inside (natural language), `#CBD5E1` at 0.3
- Label: "Generate prompt" — Inter, 11px, `#E2E8F0` at 0.5, centered below
- Sublabel: `pdd update` — JetBrains Mono, 9px, `#64748B` at 0.3

##### Step 2: "Add Tests" at (540, 420)
- Icon: 3 amber wall rectangles, 8×30px, `#D9944A` at 0.5, arranged in row
- Label: "Add tests" — Inter, 11px, `#E2E8F0` at 0.5
- Sublabel: `pdd bug` — JetBrains Mono, 9px, `#64748B` at 0.3

##### Step 3: "Regenerate" at (880, 420)
- Icon: terminal window, 55×45px, `#0F172A` fill, `#334155` border
- Inside: `pdd generate` text, 7px, `#5AAA6E` at 0.4
- Particle burst: 5 small particles (`#4A90D9` at 0.3) emanating downward (code flowing out)
- Label: "Regenerate" — Inter, 11px, `#E2E8F0` at 0.5
- Sublabel: `pdd fix` — JetBrains Mono, 9px, `#64748B` at 0.3

##### Step 4: "Compare" at (1220, 420)
- Icon: split diff view, 60×45px
- Left half: faint gray code lines (original), right half: faint blue code lines (regenerated)
- Green checkmark over each half, `#5AAA6E` at 0.5, 12px
- Label: "Compare" — Inter, 11px, `#E2E8F0` at 0.5
- Sublabel: `pdd test` — JetBrains Mono, 9px, `#64748B` at 0.3

#### Connecting Arrows
- Curved arrows between each step pair, `#334155` at 0.3, 1.5px
- Arrow heads: 6px, filled
- Light up to `#4A90D9` at 0.5 as animation progresses through each step

#### Loop Arrow (step 4 → step 2)
- Large curved arrow arcing above the pipeline from (1220, 380) back to (540, 380)
- Color: `#D9944A` at 0.3
- Dashed line: 4px dash, 4px gap
- Label at apex: "iterate" — Inter, 9px, `#D9944A` at 0.4

#### Progress Bar
- Position: centered at y: 620, width: 1100px, height: 6px
- Track: `#1E293B`, rounded 3px
- Fill: gradient from `#4A90D9` to `#5AAA6E`, rounded 3px

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Pipeline skeleton appears — empty step positions with connecting arrows in dim state.
2. **Frame 20-50 (0.67-1.67s):** Step 1 lights up. Document icon appears. Arrow to step 2 illuminates. Progress bar fills to 25%.
3. **Frame 50-80 (1.67-2.67s):** Step 2 lights up. Wall icons appear one by one. Arrow to step 3 illuminates. Progress to 50%.
4. **Frame 80-110 (2.67-3.67s):** Step 3 lights up. Terminal icon appears, particles burst out. Arrow to step 4 illuminates. Progress to 75%.
5. **Frame 110-140 (3.67-4.67s):** Step 4 lights up. Diff view appears, green checkmarks pop in. Progress to 100%.
6. **Frame 140-165 (4.67-5.5s):** Loop arrow draws from step 4 back to step 2. "iterate" label fades in. Progress bar resets to 80% with a subtle shimmer.
7. **Frame 165-180 (5.5-6s):** Hold. Pipeline complete with loop visible.

### Typography
- Step labels: Inter, 11px, `#E2E8F0` at 0.5
- Step sublabels: JetBrains Mono, 9px, `#64748B` at 0.3
- Loop label: Inter, 9px, `#D9944A` at 0.4

### Easing
- Step light-up: `easeOut(cubic)` over 15 frames
- Icon appear: `easeOut(cubic)` scale 0 → 1, 12 frames
- Arrow illuminate: `easeOut(quad)` draw, 10 frames
- Progress fill: `easeOut(quad)` per segment
- Loop arrow draw: `easeInOut(cubic)` over 20 frames
- Checkmark pop: `easeOut(back)` scale, 8 frames (slight overshoot)

## Narration Sync
> "Start with one module. Generate its prompt. Add tests. Regenerate. Compare. When the regenerated version passes all tests, the prompt is your new source of truth for that module."

Segment: `where_to_start_002`

- **23:38** ("Start with one module"): Step 1 lights up
- **23:39** ("Generate its prompt"): Step 1 fully visible, arrow to step 2
- **23:40** ("Add tests"): Step 2 lights up, walls appear
- **23:41** ("Regenerate"): Step 3 lights up, particles
- **23:42** ("Compare"): Step 4 lights up, checkmarks
- **23:43** ("the prompt is your new source of truth"): Loop arrow visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Pipeline skeleton */}
    <PipelineArrows
      positions={[[200, 420], [540, 420], [880, 420], [1220, 420]]}
      color="#334155" opacity={0.3} headSize={6} />

    {/* Step 1: Generate prompt */}
    <Sequence from={20}>
      <PipelineStep position={[200, 420]}
        illuminateArrowTo={1} arrowDuration={10}>
        <ScaleIn duration={12}>
          <PromptDocIcon size={[50, 65]} color="#4A90D9"
            lineCount={4} lineColor="#CBD5E1" />
        </ScaleIn>
        <Text text="Generate prompt" font="Inter" size={11}
          color="#E2E8F0" opacity={0.5} y={470} />
        <Text text="pdd update" font="JetBrains Mono" size={9}
          color="#64748B" opacity={0.3} y={488} />
      </PipelineStep>
    </Sequence>

    {/* Step 2: Add tests */}
    <Sequence from={50}>
      <PipelineStep position={[540, 420]}
        illuminateArrowTo={2} arrowDuration={10}>
        <StaggeredScaleIn stagger={4} duration={10}>
          <WallIcon size={[8, 30]} color="#D9944A" opacity={0.5} />
          <WallIcon size={[8, 30]} color="#D9944A" opacity={0.5} />
          <WallIcon size={[8, 30]} color="#D9944A" opacity={0.5} />
        </StaggeredScaleIn>
        <Text text="Add tests" font="Inter" size={11}
          color="#E2E8F0" opacity={0.5} y={470} />
        <Text text="pdd bug" font="JetBrains Mono" size={9}
          color="#64748B" opacity={0.3} y={488} />
      </PipelineStep>
    </Sequence>

    {/* Step 3: Regenerate */}
    <Sequence from={80}>
      <PipelineStep position={[880, 420]}
        illuminateArrowTo={3} arrowDuration={10}>
        <ScaleIn duration={12}>
          <TerminalIcon size={[55, 45]} text="pdd generate"
            textColor="#5AAA6E" />
        </ScaleIn>
        <ParticleBurst count={5} color="#4A90D9" opacity={0.3}
          direction="down" spread={30} />
        <Text text="Regenerate" font="Inter" size={11}
          color="#E2E8F0" opacity={0.5} y={470} />
        <Text text="pdd fix" font="JetBrains Mono" size={9}
          color="#64748B" opacity={0.3} y={488} />
      </PipelineStep>
    </Sequence>

    {/* Step 4: Compare */}
    <Sequence from={110}>
      <PipelineStep position={[1220, 420]}>
        <ScaleIn duration={12}>
          <DiffView size={[60, 45]}
            leftColor="#64748B" rightColor="#4A90D9" />
        </ScaleIn>
        <CheckmarkPop color="#5AAA6E" size={12} delay={8} />
        <Text text="Compare" font="Inter" size={11}
          color="#E2E8F0" opacity={0.5} y={470} />
        <Text text="pdd test" font="JetBrains Mono" size={9}
          color="#64748B" opacity={0.3} y={488} />
      </PipelineStep>
    </Sequence>

    {/* Loop arrow */}
    <Sequence from={140}>
      <DrawArc from={[1220, 380]} to={[540, 380]}
        arcHeight={-100} color="#D9944A" opacity={0.3}
        dash={[4, 4]} drawDuration={20} headSize={6}>
        <FadeIn duration={10}>
          <Text text="iterate" font="Inter" size={9}
            color="#D9944A" opacity={0.4} y={310} x={880} />
        </FadeIn>
      </DrawArc>
    </Sequence>

    {/* Progress bar */}
    <ProgressBar y={620} width={1100} height={6}
      trackColor="#1E293B"
      fillGradient={['#4A90D9', '#5AAA6E']}
      keyframes={[
        { frame: 20, value: 0 },
        { frame: 50, value: 0.25 },
        { frame: 80, value: 0.5 },
        { frame: 110, value: 0.75 },
        { frame: 140, value: 1.0 },
        { frame: 155, value: 0.8 }
      ]} />
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "workflow_pipeline",
  "steps": [
    { "label": "Generate prompt", "command": "pdd update", "icon": "prompt_doc" },
    { "label": "Add tests", "command": "pdd bug", "icon": "wall_icons" },
    { "label": "Regenerate", "command": "pdd fix", "icon": "terminal" },
    { "label": "Compare", "command": "pdd test", "icon": "diff_view" }
  ],
  "loopFrom": 3,
  "loopTo": 1,
  "loopLabel": "iterate",
  "progressBar": true,
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_002"]
}
```

---
