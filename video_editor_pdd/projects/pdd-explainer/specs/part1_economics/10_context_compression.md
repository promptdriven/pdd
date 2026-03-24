[Remotion]

# Section 1.10: Context Compression — Twenty Modules Fit as Prompts

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 4:50 - 5:10

## Visual Description

An animated visualization showing twenty code blocks — each representing a module — trying to fit into a context window rectangle. They overflow; the window is too small. The blocks stack and pile up, with several spilling over the edges, highlighted red.

Then the transformation: each code block compresses into a compact prompt block (roughly 1/5 to 1/10 the size). The twenty compact prompt blocks all fit comfortably inside the same context window, with visible empty space remaining. A label appears: "Same system. 5-10× more fits."

This is the practical demonstration of the theoretical argument — making the abstract size advantage concrete.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid lines

### Chart/Visual Elements

#### Context Window Rectangle
- Size: 600×500px, centered at (960, 500)
- Border: 2px, `#4A90D9` at 0.5
- Corner brackets: L-shapes, `#4A90D9` at 0.7
- Label: "Context Window" — Inter, 11px, `#4A90D9` at 0.5, above rectangle

#### Code Blocks (Phase 1 — Overflow)
- 20 blocks, each 120×80px
- Color: `#334155` at 0.6, 1px border `#475569` at 0.3
- Internal: faint code lines (horizontal stripes, `#475569` at 0.1)
- Module labels: JetBrains Mono, 7px, `#94A3B8` at 0.4 — "module_01" through "module_20"
- First ~8 blocks fit inside window
- Remaining ~12 blocks overflow outside, highlighted `#EF4444` at 0.15 border, with red "overflow" markers

#### Prompt Blocks (Phase 2 — Compressed)
- 20 blocks, each 50×30px (approximately 1/5 to 1/10 the visual area)
- Color: `#4A90D9` at 0.15, 1px border `#4A90D9` at 0.3
- Internal: single line suggesting natural language, `#4A90D9` at 0.1
- All 20 fit neatly inside the context window in a 5×4 grid
- Empty space visible: `#0F172A` at 0.2, labeled "Headroom"

#### Compression Arrow
- Large morphing arrow showing the transition
- Color: `#E2E8F0` at 0.3, animated

#### Result Label
- "Same system. 5-10× more fits." — Inter, 20px, bold (700), `#E2E8F0` at 0.8, centered at y: 850

### Animation Sequence
1. **Frame 0-60 (0-2s):** Context window rectangle draws. "Context Window" label appears.
2. **Frame 60-180 (2-6s):** Code blocks fly in one by one, trying to fill the window. First 8 land inside. Blocks 9-20 pile up outside the boundary, turning red-highlighted.
3. **Frame 180-240 (6-8s):** Hold on overflow state. A red "×" marker on the overflow blocks. The system doesn't fit.
4. **Frame 240-360 (8-12s):** Transformation begins — each code block morphs/shrinks into a smaller prompt block. The morph is smooth: blocks scale down, color shifts from gray to blue.
5. **Frame 360-420 (12-14s):** All 20 prompt blocks rearrange into a neat 5×4 grid inside the window. Empty space visible.
6. **Frame 420-480 (14-16s):** "Headroom" label appears in the empty space. Green checkmark replaces the red ×.
7. **Frame 480-540 (16-18s):** "Same system. 5-10× more fits." label fades in below.
8. **Frame 540-600 (18-20s):** Hold. Prompt blocks gently pulse blue.

### Typography
- Context window label: Inter, 11px, `#4A90D9` at 0.5
- Module labels: JetBrains Mono, 7px, `#94A3B8` at 0.4
- Headroom label: Inter, 10px, `#4ADE80` at 0.4
- Result label: Inter, 20px, bold (700), `#E2E8F0` at 0.8

### Easing
- Window draw: `easeOut(cubic)` over 20 frames
- Block fly-in: `easeOut(back)` staggered 6 frames each
- Overflow highlight: `easeOut(quad)` over 10 frames
- Block morph/shrink: `easeInOut(cubic)` over 40 frames per block, staggered 3 frames
- Grid rearrange: `spring(170, 26)` over 40 frames
- Result label fade: `easeOut(quad)` over 20 frames
- Prompt pulse: `easeInOut(sine)` on 50-frame cycle

## Narration Sync
> "We saw this firsthand. A team optimizing ad delivery latency had twenty modules on the critical path. As code, they overflowed the context window."
> "As prompts—a fifth to a tenth the size—they all fit."

Segments: `part1_economics_029`, `part1_economics_030`

- **4:50** ("twenty modules"): Code blocks fly in, overflow
- **5:00** ("overflowed the context window"): Hold on overflow state
- **5:03** ("As prompts"): Blocks compress into prompt blocks
- **5:07** ("they all fit"): All fit inside, result label appears

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Context window rectangle */}
    <ContextWindowBox width={600} height={500}
      center={[960, 500]}
      borderColor="#4A90D9" borderOpacity={0.5}
      cornerBrackets label="Context Window" />

    {/* Phase 1: Code blocks overflow */}
    <Sequence from={60} durationInFrames={180}>
      <StaggeredFlyIn items={codeBlocks} stagger={6}
        itemWidth={120} itemHeight={80}
        color="#334155" opacity={0.6}
        overflowColor="#EF4444" overflowOpacity={0.15}
        maxInside={8} />
    </Sequence>

    {/* Overflow marker */}
    <Sequence from={180} durationInFrames={60}>
      <FadeIn duration={10}>
        <OverflowMarker symbol="×" color="#EF4444"
          position={[1300, 500]} />
      </FadeIn>
    </Sequence>

    {/* Phase 2: Morph to prompt blocks */}
    <Sequence from={240}>
      <MorphBlocks
        from={codeBlocks} to={promptBlocks}
        fromSize={[120, 80]} toSize={[50, 30]}
        fromColor="#334155" toColor="#4A90D9"
        morphDuration={40} stagger={3}
        gridCols={5} gridRows={4}
        targetCenter={[960, 500]} />
    </Sequence>

    {/* Headroom label + checkmark */}
    <Sequence from={420}>
      <FadeIn duration={15}>
        <Text text="Headroom" font="Inter" size={10}
          color="#4ADE80" opacity={0.4}
          x={960} y={700} align="center" />
        <Icon type="checkmark" color="#4ADE80"
          position={[1300, 500]} />
      </FadeIn>
    </Sequence>

    {/* Result label */}
    <Sequence from={480}>
      <FadeIn duration={20}>
        <Text text="Same system. 5-10× more fits."
          font="Inter" size={20} weight={700}
          color="#E2E8F0" opacity={0.8}
          x={960} y={850} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "context_compression",
  "moduleCount": 20,
  "codeBlockSize": { "width": 120, "height": 80 },
  "promptBlockSize": { "width": 50, "height": 30 },
  "compressionRatio": "5-10×",
  "contextWindow": { "width": 600, "height": 500 },
  "overflowCount": 12,
  "resultLabel": "Same system. 5-10× more fits.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part1_economics_029", "part1_economics_030"]
}
```

---
