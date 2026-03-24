[Remotion]

# Section 1.5: Context Window Shrink — The Coverage Collapse

**Tool:** Remotion
**Duration:** ~30s (900 frames @ 30fps)
**Timestamp:** 2:38 - 3:08

## Visual Description

A new visualization morphs from the code cost chart. A glowing rectangular "context window" appears over a small codebase represented as a 4×4 grid of code blocks. The window covers most of the grid (~80%). Then the grid grows: 4×4 → 8×8 → 16×16 → 32×32, while the context window stays the SAME SIZE. A counter shows coverage dropping: 80% → 40% → 10% → 2%.

After the grid reaches 32×32, a detail view highlights the problem: inside the tiny window, some blocks are red (irrelevant code the AI grabbed), while outside the window, green-highlighted blocks show the code that was actually needed but couldn't be seen.

This animation makes the abstract problem of context rot viscerally visual.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid lines (the code blocks ARE the grid)

### Chart/Visual Elements

#### Code Block Grid
- Individual block size: starts at 60×60px (4×4 grid), shrinks proportionally as grid grows
- Block color: `#1E293B` at 0.6, 1px border `#334155` at 0.3
- Block internal: faint horizontal lines suggesting code — `#334155` at 0.15
- Grid centered at (960, 540)

#### Context Window Overlay
- Fixed size: 260×260px
- Border: 2px, `#4A90D9` at 0.7
- Corner markers: small L-shapes at each corner, `#4A90D9` at 0.9
- Inner glow: `#4A90D9` at 0.06
- Label: "Context Window" — Inter, 10px, `#4A90D9` at 0.6, above the rectangle

#### Coverage Counter
- Position: upper-right corner (1600, 120)
- "Context coverage:" — Inter, 12px, `#94A3B8` at 0.5
- Percentage: JetBrains Mono, 36px, bold, color transitions from `#4ADE80` (80%) → `#FBBF24` (40%) → `#EF4444` (10%) → `#DC2626` (2%)

#### Grid Size Stages
- 4×4: 16 blocks, 60×60px each = 240×240px total — window covers ~80%
- 8×8: 64 blocks, 30×30px each = 240×240px total grid area grows to 480×480
- 16×16: 256 blocks, 15×15px each = grid 480×480, window now tiny relative
- 32×32: 1024 blocks, 7.5×7.5px each = grid 480×480, window is a speck

#### Retrieval Error Highlights (at 32×32 stage)
- Inside window: 3-4 blocks highlighted `#EF4444` at 0.4 (irrelevant code grabbed)
- Outside window: 5-6 blocks highlighted `#4ADE80` at 0.4 (needed code invisible)
- Red label: "Irrelevant" — Inter, 9px, `#EF4444` at 0.6
- Green label: "Needed but invisible" — Inter, 9px, `#4ADE80` at 0.6

### Animation Sequence
1. **Frame 0-60 (0-2s):** Previous chart morphs — lines dissolve, a 4×4 grid of code blocks fades in at center. Context window rectangle appears, covering ~80% of the grid.
2. **Frame 60-90 (2-3s):** Coverage counter appears: "80%". Green color. Brief hold — AI covers everything.
3. **Frame 90-210 (3-7s):** Grid transitions to 8×8 — blocks subdivide and spread. Context window stays SAME SIZE. Counter animates: 80% → 40%. Color shifts to yellow.
4. **Frame 210-360 (7-12s):** Grid grows to 16×16. Window is now clearly smaller relative to grid. Counter: 40% → 10%. Color shifts to red.
5. **Frame 360-510 (12-17s):** Grid grows to 32×32 — a massive field of tiny blocks. Window is a tiny rectangle. Counter: 10% → 2%. Deep red.
6. **Frame 510-660 (17-22s):** Zoom into the 32×32 grid. Red-highlighted blocks appear inside the window. Green-highlighted blocks appear outside. Labels appear.
7. **Frame 660-900 (22-30s):** Hold on the complete visualization. The contrast between what the AI sees and what it needs is stark.

### Typography
- Context window label: Inter, 10px, `#4A90D9` at 0.6
- Coverage counter label: Inter, 12px, `#94A3B8` at 0.5
- Coverage percentage: JetBrains Mono, 36px, bold, color-coded
- Retrieval error labels: Inter, 9px, respective colors at 0.6

### Easing
- Grid morph/subdivide: `easeInOut(cubic)` over 60 frames
- Counter number change: `easeOut(quad)` over 30 frames
- Counter color transition: `easeOut(quad)` over 20 frames
- Red/green highlight appear: `easeOut(quad)` over 15 frames
- Zoom into grid: `easeInOut(cubic)` over 40 frames

## Narration Sync
> "But there's a second kind of debt hiding in there. One that's specific to AI-assisted development."
> "When your codebase is small, AI tools are brilliant. The context window covers almost everything."
> "But codebases grow. And that window? It stays the same size."
> "So now the AI has to guess what's relevant. Tools like Cursor use embeddings. Claude Code uses agentic search."

Segments: `part1_economics_017`, `part1_economics_018`, `part1_economics_019`, `part1_economics_020`

- **2:38** ("second kind of debt"): Chart begins morphing into grid
- **2:44** ("codebase is small"): 4×4 grid with window covering 80%
- **2:56** ("codebases grow"): Grid expands through stages, coverage counter drops
- **3:08** ("AI has to guess"): Red/green highlights appear showing retrieval errors

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={900}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Code block grid — morphs through stages */}
    <CodeBlockGrid
      stages={[
        { size: 4, blockPx: 60, startFrame: 0 },
        { size: 8, blockPx: 30, startFrame: 90 },
        { size: 16, blockPx: 15, startFrame: 210 },
        { size: 32, blockPx: 7.5, startFrame: 360 }
      ]}
      blockColor="#1E293B" blockOpacity={0.6}
      borderColor="#334155" borderOpacity={0.3}
      center={[960, 540]}
      morphDuration={60} />

    {/* Fixed-size context window */}
    <ContextWindowOverlay
      width={260} height={260}
      center={[960, 540]}
      borderColor="#4A90D9" borderOpacity={0.7}
      glowColor="#4A90D9" glowOpacity={0.06}
      cornerMarkers label="Context Window" />

    {/* Coverage counter */}
    <Sequence from={60}>
      <CoverageCounter
        position={[1600, 120]}
        stages={[
          { value: 80, color: '#4ADE80', frame: 0 },
          { value: 40, color: '#FBBF24', frame: 90 },
          { value: 10, color: '#EF4444', frame: 210 },
          { value: 2, color: '#DC2626', frame: 360 }
        ]}
        font="JetBrains Mono" size={36}
        labelFont="Inter" labelSize={12} />
    </Sequence>

    {/* Retrieval error highlights */}
    <Sequence from={510}>
      <RetrievalErrors
        insideWindow={[
          { row: 14, col: 15, type: 'irrelevant' },
          { row: 15, col: 14, type: 'irrelevant' },
          { row: 16, col: 16, type: 'irrelevant' }
        ]}
        outsideWindow={[
          { row: 3, col: 5, type: 'needed' },
          { row: 8, col: 28, type: 'needed' },
          { row: 22, col: 10, type: 'needed' },
          { row: 27, col: 20, type: 'needed' },
          { row: 30, col: 4, type: 'needed' }
        ]}
        irrelevantColor="#EF4444"
        neededColor="#4ADE80"
        opacity={0.4} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "context_window_shrink",
  "stages": [
    { "gridSize": 4, "blockPx": 60, "coveragePercent": 80, "color": "#4ADE80" },
    { "gridSize": 8, "blockPx": 30, "coveragePercent": 40, "color": "#FBBF24" },
    { "gridSize": 16, "blockPx": 15, "coveragePercent": 10, "color": "#EF4444" },
    { "gridSize": 32, "blockPx": 7.5, "coveragePercent": 2, "color": "#DC2626" }
  ],
  "contextWindow": { "width": 260, "height": 260, "color": "#4A90D9" },
  "retrievalErrors": {
    "irrelevantInside": 3,
    "neededOutside": 5,
    "irrelevantColor": "#EF4444",
    "neededColor": "#4ADE80"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part1_economics_017", "part1_economics_018", "part1_economics_019", "part1_economics_020"]
}
```

---
