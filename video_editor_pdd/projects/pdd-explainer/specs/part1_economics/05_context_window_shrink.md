[Remotion]

# Section 1.5: Context Window Shrink — The Grid That Outgrows the Window

**Tool:** Remotion
**Duration:** ~22s (660 frames @ 30fps)
**Timestamp:** 3:37 - 3:59

## Visual Description

The chart morphs into a new visualization. A glowing rectangular "context window" frame appears over a small codebase represented as a 4x4 grid of code blocks. The window covers ~80% of the grid. Each block is a stylized code-file icon with faint monospace text inside.

Then the codebase grows: 4x4 → 8x8 → 16x16 → 32x32. The context window stays the SAME SIZE. A counter shows coverage dropping: "Context coverage: 80% → 40% → 10% → 2%." The window becomes a tiny rectangle over a massive grid — the visual metaphor for why AI tools degrade on large codebases.

Inside the tiny window at the 32x32 stage, some blocks flash red — irrelevant code that the AI grabbed. Outside the window, green-highlighted blocks show the code that was actually needed but couldn't be seen. The AI is guessing, and guessing wrong.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: None (the grid IS the content)

### Chart/Visual Elements

#### Code Block Grid
- **4x4 stage:** 16 blocks, each 100x100px, gap 8px, centered at (960, 480)
  - Block style: rounded rect 6px, `#1E293B` fill, 1px `#334155` border
  - Faint monospace text lines inside: 5 lines per block, `#475569` at 0.15
- **8x8 stage:** 64 blocks, each 50x50px, gap 4px, same center
- **16x16 stage:** 256 blocks, each 25x25px, gap 2px, same center
- **32x32 stage:** 1024 blocks, each 12x12px, gap 1px, same center

#### Context Window Frame
- Fixed size: 340x340px
- Border: 2px, `#4A90D9` at 0.7
- Glow: 16px Gaussian blur, `#4A90D9` at 0.12
- Corner markers: 8px L-shapes at each corner, `#4A90D9` at 0.9
- Stays the same size throughout all grid stages

#### Coverage Counter
- Position: top-right, (1620, 100)
- "Context coverage:" — Inter, 14px, `#94A3B8` at 0.5
- Percentage: Inter, 36px, bold (700) — color transitions from `#5AAA6E` (80%) to `#D9944A` (40%) to `#EF4444` (10%, 2%)
- Percentage animates between values with number-scroll effect

#### Incorrect Retrieval (32x32 stage)
- Inside window: 8-12 random blocks flash `#EF4444` at 0.3 (red — irrelevant code grabbed)
- Outside window: 5-8 scattered blocks glow `#5AAA6E` at 0.3 (green — needed code missed)
- Small labels on red blocks: "irrelevant" — Inter, 7px, `#EF4444` at 0.4
- Small labels on green blocks: "needed" — Inter, 7px, `#5AAA6E` at 0.4

### Animation Sequence
1. **Frame 0-60 (0-2s):** Previous chart dissolves. 4x4 grid assembles — blocks pop in with stagger. Context window frame fades in, covering most of the grid. Counter shows "80%."
2. **Frame 60-120 (2-4s):** Hold. The window comfortably covers the small codebase. This is the "AI tools are brilliant" state.
3. **Frame 120-210 (4-7s):** Grid morphs to 8x8. Blocks shrink and multiply. Context window stays the same size. Coverage counter scrolls to "40%." A gap appears around the window edges.
4. **Frame 210-300 (7-10s):** Grid morphs to 16x16. Blocks shrink further. Coverage scrolls to "10%." The window is now clearly smaller than the grid. Blocks outside are dimmer.
5. **Frame 300-420 (10-14s):** Grid morphs to 32x32. The grid fills the screen. The context window is a small rectangle in the center. Coverage scrolls to "2%." The contrast is dramatic.
6. **Frame 420-540 (14-18s):** Red blocks flash inside the window (irrelevant code). Green blocks glow outside (needed code). The AI is seeing the wrong things and missing the right things.
7. **Frame 540-660 (18-22s):** Hold on the full picture. A subtle annotation appears: "Same tools. Different codebase size." The window pulses gently.

### Typography
- Coverage label: Inter, 14px, `#94A3B8` at 0.5
- Coverage percentage: Inter, 36px, bold (700), color-coded
- Block labels: Inter, 7px, respective colors at 0.4
- Annotation: Inter, 14px, `#CBD5E1` at 0.5

### Easing
- Grid morph (block shrink/multiply): `easeInOut(cubic)` over 60 frames
- Context window size hold: none (stays constant)
- Coverage counter scroll: `easeOut(cubic)` with number interpolation
- Red/green block flash: `easeOut(quad)` over 10 frames per block, staggered
- Grid assembly stagger: 2-frame delay per block, `easeOut(back(1.2))`

## Narration Sync
> "When your codebase is small, AI tools are brilliant. The context window covers almost everything."
> "But codebases grow. And that window? It stays the same size. A typical enterprise codebase spans millions of tokens. Even the largest context windows hold a fraction of that."
> "So now the AI has to guess what's relevant. Tools like Cursor use embeddings. Claude Code uses agentic search. When Jolt AI benchmarked these tools on real codebases like Django and Kubernetes, pure vector search failed to find the right files."

Segment: `part1_005`

- **3:37** ("When your codebase is small"): 4x4 grid visible, window covers most of it
- **3:41** ("But codebases grow"): Grid grows to 8x8, then 16x16
- **3:46** ("that window stays the same size"): Grid at 32x32, window is tiny
- **3:50** ("the AI has to guess"): Red/green blocks appear showing incorrect retrieval
- **3:55** ("pure vector search failed"): Hold on full picture

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={660}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Code block grid — morphs through stages */}
    <CodeBlockGrid
      stages={[
        { gridSize: 4, blockSize: 100, gap: 8, startFrame: 0 },
        { gridSize: 8, blockSize: 50, gap: 4, startFrame: 120 },
        { gridSize: 16, blockSize: 25, gap: 2, startFrame: 210 },
        { gridSize: 32, blockSize: 12, gap: 1, startFrame: 300 }
      ]}
      center={[960, 480]}
      blockColor="#1E293B" borderColor="#334155"
      morphDuration={60}
    />

    {/* Context window frame — stays fixed size */}
    <Sequence from={0}>
      <ContextWindowFrame
        center={[960, 480]} size={[340, 340]}
        borderColor="#4A90D9" borderWidth={2}
        glowRadius={16} glowOpacity={0.12}
        cornerMarkers={true}
      />
    </Sequence>

    {/* Coverage counter */}
    <Sequence from={0}>
      <CoverageCounter
        position={[1620, 100]}
        keyframes={[
          { frame: 0, value: 80, color: '#5AAA6E' },
          { frame: 120, value: 40, color: '#D9944A' },
          { frame: 210, value: 10, color: '#EF4444' },
          { frame: 300, value: 2, color: '#EF4444' }
        ]}
      />
    </Sequence>

    {/* Incorrect retrieval highlights */}
    <Sequence from={420}>
      <RetrievalHighlights
        insideWindow={{
          blocks: [3,7,12,18,24,29,35,41,48,55,60,67],
          color: '#EF4444', opacity: 0.3, label: 'irrelevant'
        }}
        outsideWindow={{
          blocks: [120,256,400,580,700,850,920,990],
          color: '#5AAA6E', opacity: 0.3, label: 'needed'
        }}
        staggerDelay={2} fadeDuration={10}
      />
    </Sequence>

    {/* Annotation */}
    <Sequence from={540}>
      <FadeIn duration={20}>
        <Text text="Same tools. Different codebase size."
          font="Inter" size={14} color="#CBD5E1" opacity={0.5}
          x={960} y={900} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "context_window_shrink",
  "gridStages": [
    { "size": "4x4", "blocks": 16, "blockPx": 100, "coverage": 0.80 },
    { "size": "8x8", "blocks": 64, "blockPx": 50, "coverage": 0.40 },
    { "size": "16x16", "blocks": 256, "blockPx": 25, "coverage": 0.10 },
    { "size": "32x32", "blocks": 1024, "blockPx": 12, "coverage": 0.02 }
  ],
  "contextWindow": {
    "fixedSize": [340, 340],
    "color": "#4A90D9"
  },
  "retrievalErrors": {
    "irrelevant": { "count": 12, "color": "#EF4444" },
    "missed": { "count": 8, "color": "#5AAA6E" }
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part1_005"]
}
```

---
