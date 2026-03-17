[Remotion]

# Section 6.2: Legacy Codebase Reveal — The Brownfield Reality

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 23:19 - 23:24

## Visual Description

A large, dense codebase visualization fills the frame. It's rendered as an interconnected file-tree / dependency graph — dozens of rectangular file blocks arranged in clusters, connected by thin dependency lines. The codebase is intentionally intimidating: tightly packed, layered, with visible entropy.

Scattered across the code blocks are red-tinted annotations that appear one by one:
- `// don't touch` on one block
- `// here be dragons` on another
- `// legacy — nobody knows what this does` on a third
- `// temporary fix (2019)` on a fourth

The overall color is a warm gray with accumulating red tint — the visual language established in Part 1 for patched code carrying technical debt. The codebase pulses faintly with a red glow suggesting accumulated complexity. This is the viewer's reality — validated, not dismissed.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### File Blocks (code modules)
- 35-45 rectangular blocks, arranged in 5-6 cluster groups
- Block sizes vary: 60×40px to 120×60px (suggesting different module sizes)
- Block fill: `#1E293B` with subtle red tint accumulating — ranges from `#1E293B` (clean) to `#2A1F1F` (heavy debt)
- Block border: `#334155` at 0.3, 1px
- ~30% of blocks have `#D9944A` at 0.06 debt glow
- Spread across 1600×800px area, centered

#### Dependency Lines
- Thin connecting lines between blocks, `#334155` at 0.15, 1px
- ~60 connections forming a tangled web
- Some lines cross each other (visual complexity)

#### Annotation Callouts
- `// don't touch` — JetBrains Mono, 10px, `#EF4444` at 0.5, positioned at (380, 320)
- `// here be dragons` — JetBrains Mono, 10px, `#EF4444` at 0.5, positioned at (1100, 250)
- `// legacy` — JetBrains Mono, 10px, `#EF4444` at 0.4, positioned at (720, 580)
- `// temporary fix (2019)` — JetBrains Mono, 10px, `#EF4444` at 0.4, positioned at (1350, 650)

#### Ambient Pulse
- Entire codebase area: radial glow `#EF4444` at 0.02, pulsing on 60-frame cycle

### Animation Sequence
1. **Frame 0-30 (0-1s):** Codebase blocks fade in from center outward, staggered by cluster. Dependency lines draw between them.
2. **Frame 30-60 (1-2s):** Red tint accumulates on ~30% of blocks — color shifts from neutral to warm. Dependency lines reach full density.
3. **Frame 60-80 (2-2.67s):** First annotation `// don't touch` fades in with a slight jitter.
4. **Frame 80-95 (2.67-3.17s):** `// here be dragons` fades in.
5. **Frame 95-110 (3.17-3.67s):** `// legacy` and `// temporary fix (2019)` fade in simultaneously.
6. **Frame 110-150 (3.67-5s):** Hold. Ambient red pulse breathes. The codebase sits there — massive, tangled, real.

### Typography
- Annotations: JetBrains Mono, 10px, `#EF4444` at 0.4-0.5
- All annotations italic

### Easing
- Block stagger: `easeOut(quad)`, 2 frames per block
- Dependency draw: `easeOut(cubic)` over 25 frames
- Red tint shift: `easeInOut(quad)` over 20 frames
- Annotation fade: `easeOut(quad)` over 12 frames, with 2px random jitter on position
- Ambient pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "Now — you don't work on a greenfield project. Nobody does."

Segment: `where_to_start_001`

- **23:19** (continuation from title card): Codebase blocks appearing
- **23:20** ("Nobody does."): Full codebase visible, annotations appearing
- **23:22** (beat): All annotations visible, the brownfield reality established

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Ambient debt pulse */}
    <PulseGlow color="#EF4444" opacity={0.02}
      radius={600} period={60} center={[960, 540]} />

    {/* File blocks — staggered appearance */}
    <Sequence from={0}>
      <CodebaseGraph
        blocks={fileBlocks} edges={dependencyEdges}
        blockFill="#1E293B" debtTint="#2A1F1F"
        debtRatio={0.3} debtGlow={{ color: '#D9944A', opacity: 0.06 }}
        borderColor="#334155" borderOpacity={0.3}
        edgeColor="#334155" edgeOpacity={0.15}
        staggerPerBlock={2} edgeDrawDuration={25}
        area={{ x: 160, y: 140, width: 1600, height: 800 }}
      />
    </Sequence>

    {/* Annotations */}
    <Sequence from={60}>
      <FadeIn duration={12}>
        <CodeComment text="// don't touch" color="#EF4444"
          opacity={0.5} position={[380, 320]} jitter={2} />
      </FadeIn>
    </Sequence>
    <Sequence from={80}>
      <FadeIn duration={12}>
        <CodeComment text="// here be dragons" color="#EF4444"
          opacity={0.5} position={[1100, 250]} jitter={2} />
      </FadeIn>
    </Sequence>
    <Sequence from={95}>
      <FadeIn duration={12}>
        <CodeComment text="// legacy" color="#EF4444"
          opacity={0.4} position={[720, 580]} jitter={2} />
      </FadeIn>
      <FadeIn duration={12}>
        <CodeComment text="// temporary fix (2019)" color="#EF4444"
          opacity={0.4} position={[1350, 650]} jitter={2} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "codebase_visualization",
  "blockCount": 40,
  "edgeCount": 60,
  "debtRatio": 0.3,
  "annotations": [
    { "text": "// don't touch", "position": [380, 320] },
    { "text": "// here be dragons", "position": [1100, 250] },
    { "text": "// legacy", "position": [720, 580] },
    { "text": "// temporary fix (2019)", "position": [1350, 650] }
  ],
  "colorScheme": {
    "clean": "#1E293B",
    "debt": "#2A1F1F",
    "annotation": "#EF4444"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_001"]
}
```

---
