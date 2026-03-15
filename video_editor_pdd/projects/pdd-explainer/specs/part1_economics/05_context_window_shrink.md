[Remotion]

# Section 1.5: Context Window Shrink — Grid Expansion Animation

**Tool:** Remotion
**Duration:** ~15s (450 frames @ 30fps)
**Timestamp:** 3:28 - 3:43

## Visual Description
A visualization showing how AI context windows become inadequate as codebases grow. A glowing rectangular "context window" sits over a small 4x4 grid of code blocks, covering ~80% of the grid. The grid then grows in stages (4x4 → 8x8 → 16x16 → 32x32) while the context window stays the same size. A live counter tracks "Context coverage: 80% → 40% → 10% → 2%". Inside the window, some blocks turn red (irrelevant code the AI grabbed); outside it, green blocks highlight code that was needed but invisible. A small inset graph in the corner shows "Performance vs. Context Length" — a steadily declining line with the EMNLP citation.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None (the code blocks ARE the grid)

### Chart/Visual Elements
- **Code Block Grid:** Centered at (960, 540)
  - Each block is a rounded rectangle with subtle code-texture (monospace glyphs at 0.1 opacity)
  - Default block fill: `#1E293B` (dark slate), border `rgba(255,255,255,0.08)`, border-radius 4px
  - Grid starts at 4x4 = 16 blocks, each block 80x80px with 4px gap
  - Grows to 8x8 (block size shrinks to 40x40px), then 16x16 (20x20px), then 32x32 (10x10px)
- **Context Window:** Glowing rectangular overlay, fixed at 320x320px
  - Border: 2px solid `#4A90D9` (blue), with `rgba(74,144,217,0.2)` glow blur 16px
  - Fill: `rgba(74,144,217,0.05)` — very subtle blue tint inside
  - Position: Centered on grid
- **Red Blocks (Irrelevant):** Inside context window, some blocks turn `rgba(239,68,68,0.5)` — irrelevant code the AI retrieved
- **Green Blocks (Missed):** Outside context window, scattered blocks turn `rgba(34,197,94,0.4)` — needed code the AI can't see
- **Coverage Counter:** Top-right corner, large text showing percentage
  - Format: "Context coverage: XX%"
  - Color transitions from `#22C55E` (green at 80%) to `#F59E0B` (amber at 40%) to `#EF4444` (red at 10% and 2%)
- **Performance Inset Graph:** Bottom-right corner, 300x180px mini chart
  - Title: "Performance vs. Context Length"
  - Single declining line from top-left to bottom-right, `#EF4444`
  - Citation below: "14-85% degradation (EMNLP, 2025)" in `#94A3B8`, 12px

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** 4x4 grid fades in. Context window appears with a gentle glow pulse. Counter shows "80%"
2. **Frame 30-60 (1.0-2.0s):** Hold — grid fully visible inside context window. This is the "AI is brilliant" state
3. **Frame 60-120 (2.0-4.0s):** Grid morphs to 8x8 — blocks shrink, new blocks appear at edges. Context window stays fixed. Counter animates 80% → 40%. Color shifts to amber
4. **Frame 120-180 (4.0-6.0s):** Grid morphs to 16x16. Context window is now a small rectangle over the large grid. Counter: 40% → 10%. Color shifts to red
5. **Frame 180-240 (6.0-8.0s):** Grid morphs to 32x32. Context window is a tiny speck. Counter: 10% → 2%. The visual impact is dramatic
6. **Frame 240-300 (8.0-10.0s):** Red blocks highlight inside the context window (3-4 blocks pulse red). Green blocks highlight outside (6-8 blocks pulse green). Shows the retrieval problem
7. **Frame 300-370 (10.0-12.33s):** Performance inset graph draws in at bottom-right. Line descends. EMNLP citation fades in
8. **Frame 370-400 (12.33-13.33s):** Annotation appears below the main grid: "Context rot" in `#F59E0B`, 24px
9. **Frame 400-450 (13.33-15.0s):** Hold final state. Everything visible

### Typography
- Coverage Counter: Inter, 32px, bold (700), color transitions green→amber→red
- "Context coverage:" Label: Inter, 20px, regular (400), `#94A3B8`
- Performance Graph Title: Inter, 14px, semi-bold (600), `#FFFFFF`, opacity 0.8
- EMNLP Citation: Inter, 12px, regular (400), `#94A3B8`
- "Context rot" Label: Inter, 24px, bold (700), `#F59E0B`

### Easing
- Grid morph: `easeInOut(cubic)` — smooth resize
- Context window glow: `easeInOut(sine)` — gentle pulse
- Counter number change: `easeOut(quad)` — smooth counting
- Red/green block highlight: `easeOut(quad)` — fade in
- Performance line draw: `easeOut(cubic)`
- Counter color transition: `linear`

## Narration Sync
> "When your codebase is small, AI tools are brilliant. The context window — what the model can actually see — covers almost everything."
> "But codebases grow. And that window? It stays the same size."
> "So now the AI has to guess what's relevant."
> "A 2025 EMNLP study proved that even when the model retrieves the right information, performance still degrades — fourteen to eighty-five percent — just from the sheer length of the input."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={450}>
  {/* Code Block Grid */}
  <CodeBlockGrid
    initialSize={4}
    stages={[
      { size: 4, startFrame: 0 },
      { size: 8, startFrame: 60 },
      { size: 16, startFrame: 120 },
      { size: 32, startFrame: 180 },
    ]}
  />

  {/* Fixed Context Window */}
  <ContextWindowOverlay
    width={320}
    height={320}
    borderColor="#4A90D9"
    glowColor="rgba(74,144,217,0.2)"
  />

  {/* Coverage Counter */}
  <CoverageCounter
    stages={[
      { frame: 0, value: 80, color: "#22C55E" },
      { frame: 60, value: 40, color: "#F59E0B" },
      { frame: 120, value: 10, color: "#EF4444" },
      { frame: 180, value: 2, color: "#EF4444" },
    ]}
  />

  {/* Red/Green Highlights */}
  <Sequence from={240} durationInFrames={60}>
    <RetrievalHighlights
      redBlocks={[3, 7, 11, 14]}
      greenBlocks={[120, 245, 389, 512, 678, 801, 903, 995]}
    />
  </Sequence>

  {/* Performance Inset */}
  <Sequence from={300} durationInFrames={70}>
    <PerformanceInsetGraph
      citation="14-85% degradation (EMNLP, 2025)"
    />
  </Sequence>

  {/* Context Rot Label */}
  <Sequence from={370}>
    <ContextRotLabel />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "gridStages": [
    { "size": 4, "blockPx": 80, "coverage": 80 },
    { "size": 8, "blockPx": 40, "coverage": 40 },
    { "size": 16, "blockPx": 20, "coverage": 10 },
    { "size": 32, "blockPx": 10, "coverage": 2 }
  ],
  "contextWindow": {
    "width": 320,
    "height": 320,
    "borderColor": "#4A90D9",
    "glowColor": "rgba(74, 144, 217, 0.2)"
  },
  "performanceGraph": {
    "title": "Performance vs. Context Length",
    "degradationRange": "14-85%",
    "citation": "EMNLP, 2025"
  },
  "backgroundColor": "#0F172A"
}
```

---
