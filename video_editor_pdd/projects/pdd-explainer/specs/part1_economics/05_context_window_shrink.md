[Remotion]

# Section 1.5: Context Window Shrink — Coverage Collapse Visualization

**Tool:** Remotion
**Duration:** ~24s (720 frames @ 30fps)
**Timestamp:** 2:44 - 3:08

## Visual Description

A striking visual demonstration of context window coverage collapse. A glowing rectangular "context window" sits over a codebase represented as a grid of code blocks.

The animation starts with a small 4x4 grid where the context window covers ~80% of the blocks. Then the grid grows: 4x4 → 8x8 → 16x16 → 32x32. The context window stays EXACTLY THE SAME SIZE. A counter in the corner ticks down: "Context coverage: 80% → 40% → 10% → 2%".

By the end, the window is a tiny glowing rectangle lost in a massive field of blocks. Inside the tiny window, some blocks highlight red (irrelevant code the AI grabbed). Outside the window, green-highlighted blocks show code that was actually needed but couldn't be seen.

The visual makes the abstract concept of context rot immediately visceral.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none (the code blocks ARE the grid)

### Chart/Visual Elements

#### Context Window
- Glowing rectangle: `#4A90D9` border 2px, glow `#4A90D9` at 0.2, 12px radius
- Fixed size: 280×200px (never changes)
- Centered initially, stays centered as grid grows around it

#### Code Block Grid
- Each block: rounded rect, 4px radius
- Default state: `#1E293B` fill, `#334155` border at 0.2
- Grid padding: 4px between blocks
- Phase 1 (4×4): 16 blocks, each ~65×45px
- Phase 2 (8×8): 64 blocks, each ~30×22px
- Phase 3 (16×16): 256 blocks, each ~14×10px
- Phase 4 (32×32): 1024 blocks, each ~6×4px (barely visible individually)

#### Coverage Counter
- Position: top-right corner, (1700, 80)
- "Context coverage:" label — Inter, 14px, `#94A3B8` at 0.5
- Percentage: Inter, 32px, bold, color transitions from `#2DD4BF` (80%) to `#EF4444` (2%)
- Animates between values with countUp/countDown effect

#### Red Highlights (inside window, irrelevant)
- 3-4 blocks inside the window glow red: `#EF4444` at 0.4
- Small label: "Irrelevant code retrieved" — Inter, 10px, `#EF4444` at 0.5

#### Green Highlights (outside window, needed)
- 6-8 blocks scattered outside the window glow green: `#22C55E` at 0.4
- Small label: "Needed code — invisible to AI" — Inter, 10px, `#22C55E` at 0.5

### Animation Sequence
1. **Frame 0-60 (0-2s):** 4×4 grid appears. Context window appears over it, covering ~80%. Counter: "80%".
2. **Frame 60-180 (2-6s):** Grid morphs to 8×8. Blocks split and shrink. Window stays same size. Counter ticks to "40%".
3. **Frame 180-360 (6-12s):** Grid morphs to 16×16. Blocks tiny now. Window feels inadequate. Counter: "10%".
4. **Frame 360-480 (12-16s):** Grid morphs to 32×32. Blocks are pixels. Window is a tiny rectangle. Counter: "2%" in red.
5. **Frame 480-600 (16-20s):** Red blocks appear inside window. Green blocks appear outside. The mismatch is visible.
6. **Frame 600-720 (20-24s):** Hold. Labels appear. The visual settles — the context window is lost in a sea of code.

### Typography
- Coverage label: Inter, 14px, `#94A3B8` at 0.5
- Coverage value: Inter, 32px, bold (700), color gradient `#2DD4BF` → `#EF4444`
- Red label: Inter, 10px, `#EF4444` at 0.5
- Green label: Inter, 10px, `#22C55E` at 0.5

### Easing
- Grid expansion: `easeInOut(cubic)` over 60 frames per phase
- Counter transition: `easeOut(quad)` countDown over 30 frames
- Context window position: stays fixed, `spring(damping: 15)` if grid pushes
- Block split: `easeOut(back)` over 40 frames — slight overshoot
- Red/green highlight appear: `easeOut(quad)` over 15 frames

## Narration Sync
> "your code base is small, the AI's context window can hold most of it. Maybe 80%. Coverage is high. Results are great."
> "But code bases grow. And the context window doesn't grow with them. 40%. 10%. Now it's grabbing blindly."
> "So now the AI has two problems. It can't see enough of the codebase to understand the full picture..."

Segments: `part1_economics_018`, `part1_economics_019`, `part1_economics_020`

- **164.22s** ("your code base is small"): 4×4 grid appears, 80% coverage
- **175.82s** ("But code bases grow"): Grid expanding, counter dropping
- **188.08s** ("So now the AI has two problems"): 32×32 grid, red/green highlights visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={720}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Code block grid — morphing */}
    <CodeBlockGrid
      phases={[
        { gridSize: 4, duration: 60, startFrame: 0 },
        { gridSize: 8, duration: 120, startFrame: 60 },
        { gridSize: 16, duration: 180, startFrame: 180 },
        { gridSize: 32, duration: 120, startFrame: 360 }
      ]}
      blockColor="#1E293B" borderColor="#334155"
      center={[960, 540]} totalArea={[800, 600]} />

    {/* Context window — fixed size */}
    <ContextWindowRect
      width={280} height={200} center={[960, 540]}
      borderColor="#4A90D9" borderWidth={2}
      glowColor="#4A90D9" glowOpacity={0.2} glowRadius={12} />

    {/* Coverage counter */}
    <Sequence from={0}>
      <CoverageCounter
        position={[1700, 80]}
        values={[
          { frame: 0, value: 80, color: "#2DD4BF" },
          { frame: 120, value: 40, color: "#F59E0B" },
          { frame: 300, value: 10, color: "#EF4444" },
          { frame: 420, value: 2, color: "#EF4444" }
        ]}
        labelFont="Inter" labelSize={14} labelColor="#94A3B8"
        valueFont="Inter" valueSize={32} valueWeight={700} />
    </Sequence>

    {/* Red highlights — irrelevant code inside window */}
    <Sequence from={480}>
      <FadeIn duration={15}>
        <HighlightBlocks
          gridRef="code_block_grid" window="inside"
          indices={[3, 7, 12, 15]}
          color="#EF4444" opacity={0.4} />
        <Text text="Irrelevant code retrieved" font="Inter" size={10}
          color="#EF4444" opacity={0.5}
          x={960} y={660} align="center" />
      </FadeIn>
    </Sequence>

    {/* Green highlights — needed code outside window */}
    <Sequence from={510}>
      <FadeIn duration={15}>
        <HighlightBlocks
          gridRef="code_block_grid" window="outside"
          indices={[45, 128, 256, 389, 512, 678, 801, 945]}
          color="#22C55E" opacity={0.4} />
        <Text text="Needed code — invisible to AI" font="Inter" size={10}
          color="#22C55E" opacity={0.5}
          x={960} y={690} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "context_window_visualization",
  "contextWindow": {
    "width": 280,
    "height": 200,
    "fixedSize": true,
    "borderColor": "#4A90D9"
  },
  "gridPhases": [
    { "size": "4x4", "blocks": 16, "coverage": 0.80, "color": "#2DD4BF" },
    { "size": "8x8", "blocks": 64, "coverage": 0.40, "color": "#F59E0B" },
    { "size": "16x16", "blocks": 256, "coverage": 0.10, "color": "#EF4444" },
    { "size": "32x32", "blocks": 1024, "coverage": 0.02, "color": "#EF4444" }
  ],
  "highlights": {
    "red": { "meaning": "irrelevant_code_retrieved", "count": 4 },
    "green": { "meaning": "needed_code_invisible", "count": 8 }
  },
  "narrationSegments": ["part1_economics_018", "part1_economics_019", "part1_economics_020"]
}
```

---
