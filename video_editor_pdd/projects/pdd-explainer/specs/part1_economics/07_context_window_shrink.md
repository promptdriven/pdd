[Remotion]

# Section 1.7: Context Window Shrink — Codebase Growth vs. Fixed Window

**Tool:** Remotion
**Duration:** ~52s (1560 frames @ 30fps)
**Timestamp:** 2:49 - 3:41

## Visual Description

The debt layers morph into a new visualization demonstrating context window limitations. A glowing rectangular "context window" hovers over a grid of code blocks representing a codebase.

**Phase 1:** Small codebase (4×4 grid). The context window covers ~80% of the grid. Everything is visible, clean, well-lit. The AI "sees" almost everything.

**Phase 2:** The grid grows: 4×4 → 8×8 → 16×16 → 32×32. The context window stays the EXACT SAME SIZE. A counter shows coverage dropping: "80% → 40% → 10% → 2%". The window shrinks to a tiny bright rectangle over a massive dark grid.

**Phase 3:** Inside the tiny window, some blocks are highlighted red — irrelevant code the AI grabbed. Outside the window, green-highlighted blocks show code that was actually needed but couldn't be seen. The mismatch is visually striking.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Code Grid
- Block size: Adapts with grid (starts at 60px, shrinks proportionally)
- Block color: `#1E293B` fill, `#334155` 1px border
- Block spacing: 4px gap
- Grid grows centered on screen

#### Context Window
- Fixed size: 280×240px (does NOT change)
- Border: `#4A90D9` 2px solid, with outer glow `#4A90D9` at 0.2, 12px blur
- Interior: `#4A90D9` at 0.05 fill (light tint on covered blocks)

#### Coverage Counter
- Position: Top-right corner, (1600, 100)
- "Context coverage:" label — Inter 14px, `#94A3B8`
- Percentage — Inter 36px, bold (700), color shifts from `#5AAA6E` (80%) → `#F59E0B` (40%) → `#EF4444` (10%) → `#DC2626` (2%)

#### Red Blocks (inside window, irrelevant)
- Fill overlay: `#EF4444` at 0.3
- Appear only in Phase 3 — 3-4 blocks inside the window highlighted red

#### Green Blocks (outside window, needed)
- Fill overlay: `#5AAA6E` at 0.3
- Appear only in Phase 3 — 5-6 blocks scattered outside the window highlighted green

### Animation Sequence
1. **Frame 0-60 (0-2s):** Chart morphs into grid visualization. 4×4 grid assembles. Context window appears, covering most of it.
2. **Frame 60-180 (2-6s):** Counter shows "80%". Context window is comfortable. Blocks inside are well-lit.
3. **Frame 180-300 (6-10s):** Grid grows to 8×8. Counter drops to "40%". Window is now covering roughly half.
4. **Frame 300-420 (10-14s):** Grid grows to 16×16. Counter drops to "10%". Window is clearly small relative to the grid.
5. **Frame 420-540 (14-18s):** Grid grows to 32×32. Counter drops to "2%". Window is a tiny bright rectangle. The grid is massive and dark.
6. **Frame 540-720 (18-24s):** Hold at 32×32. The tiny window emphasizes the scale mismatch.
7. **Frame 720-900 (24-30s):** Red blocks appear inside window (irrelevant code grabbed). Green blocks appear outside (needed code missed). The mismatch is stark.
8. **Frame 900-1560 (30-52s):** Hold. Narration covers agentic search, Jolt AI benchmarks, and retrieval challenges.

### Typography
- Coverage counter: Inter, 36px, bold (700), color-coded
- Coverage label: Inter, 14px, regular (400), `#94A3B8`
- Red block tooltip: "Irrelevant" — Inter 11px, `#EF4444` at 0.7
- Green block tooltip: "Needed" — Inter 11px, `#5AAA6E` at 0.7

### Easing
- Grid growth: `easeInOut(cubic)` — blocks scale/reposition over 60 frames each
- Counter number: `spring(stiffness: 100)` — snappy number change
- Counter color shift: `easeOut(quad)` over 30 frames
- Red/green highlights: `easeOut(quad)` over 20 frames, slight scale 0.95 → 1.0

## Narration Sync
> "When your codebase is small, AI tools are brilliant. The context window covers almost everything."
> "But codebases grow. And that window? It stays the same size."
> "So now the AI has to guess what's relevant. Tools like Cursor use embeddings. Claude Code uses agentic search — grep, file by file."

Segments: `part1_economics_014`, `part1_economics_015`, `part1_economics_016`

- **168.86s** (seg 014): 4×4 grid appears — "When your codebase is small"
- **181.54s** (seg 014 ends): Grid at 4×4, 80% coverage
- **181.54s** (seg 015): Grid growing — "But codebases grow"
- **194.02s** (seg 015 ends): Grid at 32×32, 2% coverage
- **194.14s** (seg 016): Red/green highlights — "So now the AI has to guess what's relevant"
- **219.82s** (seg 016 ends): Mismatch fully visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1560}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Growing code grid */}
    <CodeBlockGrid
      growthStages={[
        { size: 4, startFrame: 0, coveragePercent: 80 },
        { size: 8, startFrame: 180, coveragePercent: 40 },
        { size: 16, startFrame: 300, coveragePercent: 10 },
        { size: 32, startFrame: 420, coveragePercent: 2 },
      ]}
      blockColor="#1E293B"
      borderColor="#334155"
      transitionDuration={60}
    />

    {/* Fixed-size context window */}
    <ContextWindow
      width={280} height={240}
      borderColor="#4A90D9" borderWidth={2}
      glowColor="#4A90D9" glowOpacity={0.2} glowBlur={12}
    />

    {/* Coverage counter */}
    <CoverageCounter
      position={{ x: 1600, y: 100 }}
      colorStops={[
        { percent: 80, color: "#5AAA6E" },
        { percent: 40, color: "#F59E0B" },
        { percent: 10, color: "#EF4444" },
        { percent: 2, color: "#DC2626" },
      ]}
    />

    {/* Red/green mismatch highlights */}
    <Sequence from={720}>
      <MismatchHighlights
        redBlocks={[3, 7, 11, 14]}
        greenBlocks={[45, 128, 312, 567, 890, 1002]}
        redColor="#EF4444" greenColor="#5AAA6E"
        opacity={0.3} fadeInDuration={20}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "context_window_visualization",
  "chartId": "context_window_shrink",
  "growthStages": [
    { "gridSize": "4x4", "coverage": 0.80, "coverageColor": "#5AAA6E" },
    { "gridSize": "8x8", "coverage": 0.40, "coverageColor": "#F59E0B" },
    { "gridSize": "16x16", "coverage": 0.10, "coverageColor": "#EF4444" },
    { "gridSize": "32x32", "coverage": 0.02, "coverageColor": "#DC2626" }
  ],
  "contextWindow": {
    "width": 280,
    "height": 240,
    "borderColor": "#4A90D9",
    "fixed": true
  },
  "mismatchPhase": {
    "irrelevantInsideCount": 4,
    "neededOutsideCount": 6
  },
  "narrationSegments": ["part1_economics_014", "part1_economics_015", "part1_economics_016"]
}
```

---
