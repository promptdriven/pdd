[Remotion]

# Section 6.4: Source of Truth — Module Shelf Animation

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 22:44 - 22:52

## Visual Description
A visualization showing modules transitioning from "code as source of truth" to "prompt as source of truth." A horizontal shelf displays 8 module blocks in a row. Initially, all blocks are code-blue with a `</>` icon. As the narration says "one module at a time," the first block flips (like a card) to reveal a golden prompt-side with a document icon. A counter reads "1 of 8." The visual holds — only one block flips, reinforcing the "start small" message. The remaining 7 blocks dim slightly, suggesting they'll follow in time. This grounds the practical advice: you don't convert everything at once.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Section Label:** "Module Shelf" — `#94A3B8`, 16px, Inter, top-left at (120, 80)
- **Module Blocks:** 8 blocks in a horizontal row, centered at Y=440
  - Block dimensions: 100px wide x 130px tall, 8px border-radius, 16px gap between
  - Total row width: 8×100 + 7×16 = 912px, starting at X=504
  - **Code side (default):** Fill `#1E293B`, stroke `#4A90D9` at 0.3 opacity, 1px
    - Icon: `</>` — `#4A90D9` at 0.4 opacity, 20px, centered
    - Label below block: "auth" / "user" / "cart" / "pay" / "ship" / "inv" / "log" / "api" — `#64748B`, 12px, JetBrains Mono
  - **Prompt side (flipped):** Fill `#1A1510`, stroke `#FBBF24` at 0.4 opacity, 1px
    - Icon: Document with lines — `#FBBF24` at 0.5 opacity, 20px, centered
    - Small checkmark badge at top-right corner of block: `#5AAA6E`, 10px
- **Counter:** "1 of 8 modules converted" — `#FFFFFF` at 0.5 opacity, 18px, Inter, centered at Y=620
- **Progress Bar:** Thin horizontal bar below counter at Y=650, 400px wide
  - Background: `rgba(255,255,255,0.08)`
  - Fill: `#FBBF24` at 0.6 opacity, width = 1/8 of total (50px)

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Module blocks fade in one by one from left to right (5-frame stagger), all showing code side. Section label fades in
2. **Frame 40-60 (1.33-2.0s):** Hold — all 8 code blocks visible
3. **Frame 60-120 (2.0-4.0s):** First block ("auth") performs a 3D card flip (rotateY 0→180°). The code side fades at 90°, prompt side appears after 90°. Block lands with golden border and document icon. Checkmark badge bounces in
4. **Frame 120-160 (4.0-5.33s):** Counter "1 of 8 modules converted" fades in. Progress bar appears and fills to 1/8
5. **Frame 160-200 (5.33-6.67s):** Remaining 7 blocks dim (opacity drops to 0.4). A subtle dotted arrow curves from block 1 toward block 2, suggesting "next" — but it stays ghosted (`rgba(255,255,255,0.1)`)
6. **Frame 200-240 (6.67-8.0s):** Hold. The converted block breathes with a gentle golden glow (0.02 opacity oscillation)

### Typography
- Section Label: Inter, 16px, regular (400), `#94A3B8`
- Module Names: JetBrains Mono, 12px, regular, `#64748B`
- Counter: Inter, 18px, regular (400), `#FFFFFF` at 0.5 opacity
- Code Icon: JetBrains Mono, 20px, regular, `#4A90D9` at 0.4 opacity
- Prompt Icon: Drawn SVG, `#FBBF24` at 0.5 opacity

### Easing
- Block stagger fade-in: `easeOut(quad)`
- Card flip: `easeInOut(cubic)` (smooth 3D rotation)
- Checkmark bounce: `spring({ damping: 12, stiffness: 200 })`
- Counter fade: `easeOut(quad)`
- Progress bar fill: `easeOut(cubic)`
- Dim remaining blocks: `easeOut(quad)`

## Narration Sync
> "One module at a time."

Segment: `where_to_start_002` (15.46s – 16.90s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  {/* Module Shelf */}
  <Sequence from={0} durationInFrames={40}>
    {modules.map((mod, i) => (
      <Sequence key={mod} from={i * 5}>
        <ModuleBlock
          name={mod}
          x={504 + i * 116}
          y={440}
          side="code"
        />
      </Sequence>
    ))}
  </Sequence>

  {/* Card Flip — First Module */}
  <Sequence from={60} durationInFrames={60}>
    <CardFlip
      targetIndex={0}
      fromSide="code"
      toSide="prompt"
      x={504}
      y={440}
    />
  </Sequence>

  {/* Counter + Progress */}
  <Sequence from={120} durationInFrames={40}>
    <Counter text="1 of 8 modules converted" y={620} />
    <ProgressBar
      total={8}
      filled={1}
      width={400}
      y={650}
      fillColor="#FBBF24"
    />
  </Sequence>

  {/* Dim remaining */}
  <Sequence from={160} durationInFrames={40}>
    <DimBlocks indices={[1,2,3,4,5,6,7]} targetOpacity={0.4} />
    <GhostArrow from={504} to={620} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "modules": ["auth", "user", "cart", "pay", "ship", "inv", "log", "api"],
  "blockSize": { "width": 100, "height": 130 },
  "gap": 16,
  "rowStartX": 504,
  "rowY": 440,
  "codeSide": {
    "fill": "#1E293B",
    "stroke": "#4A90D9",
    "icon": "</>",
    "iconColor": "#4A90D9"
  },
  "promptSide": {
    "fill": "#1A1510",
    "stroke": "#FBBF24",
    "icon": "document",
    "iconColor": "#FBBF24"
  },
  "counter": {
    "text": "1 of 8 modules converted",
    "y": 620
  },
  "progressBar": {
    "total": 8,
    "filled": 1,
    "width": 400,
    "y": 650
  }
}
```

---
