[Remotion]

# Section 1.12: Context Compression — 20 Modules Fit as Prompts

**Tool:** Remotion
**Duration:** ~46s (1380 frames @ 30fps)
**Timestamp:** 6:24 - 7:10

## Visual Description

An animation demonstrating the practical advantage of working in prompt space. Twenty code blocks (each representing a module) attempt to fit into a context window — and overflow. Then the same twenty modules, represented as compact prompt blocks, all fit comfortably with room to spare.

**Phase 1:** Twenty rectangular code blocks (dark gray, various sizes ~200-400px tall) slide toward a fixed-size context window frame. They stack up — the first 3-4 fit, then the rest overflow past the window boundary. Red overflow indicators appear. Label: "20 modules as code — doesn't fit."

**Phase 2:** The code blocks compress/morph into compact prompt blocks (blue, ~40-80px tall each). They rearrange inside the same window — all twenty fit easily. Green space remains at the bottom. Label: "Same system. 5-10× more fits."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Context Window Frame
- Size: 500×700px, centered at (960, 480)
- Border: `#4A90D9`, 2px solid, 8px corner radius
- Glow: `#4A90D9` at 0.1, 8px blur

#### Code Blocks (Phase 1)
- 20 blocks, `#1E293B` fill, `#334155` 1px border
- Varying heights: 180-350px (representing code size)
- Total height if stacked: ~5000px (overflows the 700px window)
- Each block labeled with module name: "auth", "parser", "router", etc. — Inter 11px, `#64748B`

#### Prompt Blocks (Phase 2)
- 20 blocks, `#4A90D9` at 0.15 fill, `#4A90D9` 1px border
- Uniform height: ~30px each (representing prompt size)
- Total height: ~660px (fits within 700px window)
- Same module names as labels

#### Overflow Indicator
- Red dashed line at window bottom: `#EF4444`, 1.5px dashed
- Red glow below: `#EF4444` at 0.1
- Count: "17 modules can't be seen" — Inter 14px, `#EF4444`

#### Remaining Space Indicator
- Green fill at window bottom: `#5AAA6E` at 0.05
- Label: "Room to spare" — Inter 12px, italic, `#5AAA6E` at 0.5

### Animation Sequence
1. **Frame 0-60 (0-2s):** Context window frame draws. "Context Window" label appears above.
2. **Frame 60-300 (2-10s):** Code blocks slide in from the left, stacking inside the window. First 3-4 fit. Blocks 5-20 overflow past the bottom edge. Red overflow line and count appear.
3. **Frame 300-420 (10-14s):** Hold on overflow. "20 modules as code — doesn't fit" label.
4. **Frame 420-600 (14-20s):** Transformation: each code block compresses vertically, changes color to blue. They morph from tall gray blocks to short blue prompt blocks. Smooth, satisfying compression animation.
5. **Frame 600-780 (20-26s):** All 20 prompt blocks rearrange inside the window. They all fit. Green space appears at the bottom. "Same system. 5-10× more fits." label appears.
6. **Frame 780-1380 (26-46s):** Hold. The visual proof is complete.

### Typography
- Module labels: Inter, 11px, regular (400), `#64748B`
- Overflow count: Inter, 14px, regular (400), `#EF4444`
- Phase labels: Inter, 18px, bold (700), `#E2E8F0`
- Ratio label: Inter, 20px, bold (700), `#5AAA6E`

### Easing
- Block slide-in: `easeOut(cubic)`, 15-frame stagger per block
- Overflow reveal: `easeOut(quad)` over 20 frames
- Block compression: `easeInOut(cubic)` over 120 frames — smooth morph
- Green fill: `easeOut(quad)` over 30 frames
- Final label: `easeOut(back)` with subtle overshoot

## Narration Sync
> "We saw this firsthand. A team optimizing ad delivery latency had twenty modules on the critical path. As code, they overflowed the context window... As prompts — a fifth to a tenth the size — they all fit."
> "Meanwhile, generation just crossed below both lines. The debt doesn't just slow down — it resets."

Segments: `part1_economics_025`, `part1_economics_026`

- **409.78s** (seg 025): Window draws, code blocks start — "We saw this firsthand"
- **420.0s**: Code blocks overflow
- **430.0s**: Compression begins — "As prompts, they all fit"
- **445.0s**: All prompt blocks fit
- **455.26s** (seg 025 ends): Hold on result
- **455.92s** (seg 026): "Meanwhile, generation just crossed below both lines"
- **467.72s** (seg 026 ends): Transition to crossing lines moment

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1380}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Context window frame */}
    <ContextWindowFrame
      width={500} height={700}
      center={{ x: 960, y: 480 }}
      borderColor="#4A90D9"
    />

    {/* Phase 1: Code blocks overflow */}
    <Sequence from={60}>
      <ModuleBlockStack
        modules={moduleList}
        blockType="code"
        blockColor="#1E293B"
        blockHeightRange={[180, 350]}
        windowHeight={700}
        slideInDuration={240}
        stagger={15}
      />
    </Sequence>

    {/* Overflow indicator */}
    <Sequence from={300}>
      <OverflowIndicator
        color="#EF4444"
        count={17}
        label="modules can't be seen"
      />
    </Sequence>

    {/* Phase 2: Compress to prompts */}
    <Sequence from={420}>
      <BlockCompression
        from={{ type: "code", color: "#1E293B", heights: codeHeights }}
        to={{ type: "prompt", color: "#4A90D9", height: 30 }}
        morphDuration={180}
      />
    </Sequence>

    {/* Result label */}
    <Sequence from={600}>
      <FadeIn duration={30}>
        <Text text="Same system. 5-10× more fits."
          font="Inter" size={20} weight={700}
          color="#5AAA6E" x={960} y={900} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "context_compression_animation",
  "chartId": "module_compression",
  "modules": [
    "auth", "parser", "router", "validator", "logger",
    "cache", "queue", "mailer", "search", "analytics",
    "billing", "permissions", "notifications", "export",
    "import", "scheduler", "webhook", "api_client",
    "transformer", "serializer"
  ],
  "codeTokensPerModule": 750,
  "promptTokensPerModule": 100,
  "contextWindowTokens": 4000,
  "overflowCount": 17,
  "compressionRatio": "5-10×",
  "narrationSegments": ["part1_economics_025", "part1_economics_026"]
}
```

---
