[split:Manual Construction vs Specification] Three Industries — Same Revolution

# Section 2.7: Split Screen — Manual Construction vs Specification-Driven

**Tool:** Remotion
**Duration:** ~12s
**Timestamp:** 2:25 - 2:37

## Visual Description
A three-column split-screen layout that crystallizes the pattern across industries. Each column represents one industry's before/after transition: (1) Textiles — hand-darning icon → factory loom icon, (2) Plastics — hand-sculpting icon → injection mold icon, (3) Semiconductors — hand-drawn gate icon → HDL code icon. Each column has a "BEFORE" row (warm amber, manual) and an "AFTER" row (cool blue, specification-driven). A horizontal divider separates them, labeled "THE SHIFT." The columns slide in sequentially from left to right, then the divider line sweeps across all three simultaneously, revealing the "AFTER" row. A bottom banner reads: "We've seen this before — we just didn't recognize it."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Layout region: full width, vertically centered, 1600x600px at (160, 240) to (1760, 840)
- Backing panel: rgba(15, 23, 42, 0.85), blur(12px), border-radius 20px

### Chart/Visual Elements
- Three columns, each 480px wide with 40px gutters:
  - Column 1: x=200-680, "TEXTILES"
  - Column 2: x=720-1200, "PLASTICS"
  - Column 3: x=1240-1720, "SEMICONDUCTORS"
- Column headers: industry name, centered at top of each column
- BEFORE row (y=340-520):
  - Background tint: rgba(249, 115, 22, 0.06)
  - Label: "BEFORE" in left margin, vertical text, #F97316 at 50% opacity
  - Column 1 icon: needle & thread silhouette, 64x64px, #F97316
  - Column 1 text: "Hand-darning" — #CBD5E1
  - Column 2 icon: hands sculpting clay, 64x64px, #F97316
  - Column 2 text: "Hand-sculpting" — #CBD5E1
  - Column 3 icon: pencil & ruler, 64x64px, #F97316
  - Column 3 text: "Hand-drawn gates" — #CBD5E1
- Divider: horizontal line at y=530, full width of layout
  - Label: "THE SHIFT" centered on divider, pill-shaped background
  - Line: 2px, gradient #F97316 → #3B82F6
- AFTER row (y=540-720):
  - Background tint: rgba(59, 130, 246, 0.06)
  - Label: "AFTER" in left margin, vertical text, #3B82F6 at 50% opacity
  - Column 1 icon: factory loom silhouette, 64x64px, #3B82F6
  - Column 1 text: "Automated weaving" — #CBD5E1
  - Column 2 icon: injection mold press, 64x64px, #3B82F6
  - Column 2 text: "Mold specification" — #CBD5E1
  - Column 3 icon: code terminal, 64x64px, #3B82F6
  - Column 3 text: "HDL + synthesis" — #CBD5E1
- Bottom banner: "We've seen this before — we just didn't recognize it."
  - Position: centered at (960, 800)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Backing panel fades in.
2. **Frame 20-50 (0.67-1.67s):** Column 1 slides in from left — translateX(-100)→0, opacity 0→1. BEFORE row icons and text for Column 1 appear.
3. **Frame 40-70 (1.33-2.33s):** Column 2 slides in — translateX(-100)→0, opacity 0→1. BEFORE row for Column 2.
4. **Frame 60-90 (2-3s):** Column 3 slides in — translateX(-100)→0, opacity 0→1. BEFORE row for Column 3.
5. **Frame 90-120 (3-4s):** Divider line sweeps left to right. "THE SHIFT" label fades in at center.
6. **Frame 120-150 (4-5s):** AFTER row reveals — all three columns simultaneously, icons scale 0→1 (spring), text fades in.
7. **Frame 150-240 (5-8s):** Hold. BEFORE row dims slightly (opacity 1.0→0.6).
8. **Frame 240-280 (8-9.33s):** Bottom banner text fades in — opacity 0→1, translateY 10→0.
9. **Frame 280-330 (9.33-11s):** Hold.
10. **Frame 330-360 (11-12s):** Entire split screen fades out — opacity 1→0.

### Typography
- Column headers: Inter Bold, 18px, #94A3B8, letter-spacing 0.12em, uppercase
- BEFORE/AFTER labels: Inter Bold, 14px, rotated -90°
  - BEFORE: #F97316 at 50% opacity
  - AFTER: #3B82F6 at 50% opacity
- Icon descriptors: Inter Medium, 16px, #CBD5E1
- "THE SHIFT" pill: Inter Black, 16px, #FFFFFF, background gradient #F97316→#3B82F6, padding 6px 20px, border-radius 12px
- Bottom banner: Inter SemiBold, 26px, #E2E8F0, italic

### Easing
- Column slides: `spring({ damping: 18, stiffness: 140 })`
- Divider sweep: `easeInOutCubic`
- AFTER icon spring: `spring({ damping: 12, stiffness: 200 })`
- BEFORE dim: `easeOutQuad`
- Banner fade: `easeOutCubic`

## Narration Sync
> "Same revolution: specification replaced manual construction."

The three-column layout builds during "same revolution" — showing textiles, plastics, and semiconductors all followed the identical pattern. The divider sweeps on "specification replaced manual construction."

## Code Structure (Remotion)
```typescript
<Sequence from={SPLIT_START} durationInFrames={360}>
  <AbsoluteFill>
    <BackingPanel
      bounds={{ x: 160, y: 240, w: 1600, h: 600 }}
      opacity={interpolate(frame, [0, 20, 330, 360], [0, 0.85, 0.85, 0])}
    />

    {/* Column 1 — Textiles */}
    <IndustryColumn
      x={200} width={480}
      header="TEXTILES"
      beforeIcon="needle_thread" beforeText="Hand-darning"
      afterIcon="factory_loom" afterText="Automated weaving"
      slideIn={interpolate(frame, [20, 50], [-100, 0], { extrapolateRight: 'clamp' })}
      opacity={interpolate(frame, [20, 50, 330, 360], [0, 1, 1, 0])}
      afterScale={frame >= 120 ? spring({ frame: frame - 120, fps: 30 }) : 0}
      beforeDim={interpolate(frame, [150, 240], [1.0, 0.6], { extrapolateRight: 'clamp' })}
    />

    {/* Column 2 — Plastics */}
    <IndustryColumn
      x={720} width={480}
      header="PLASTICS"
      beforeIcon="hands_sculpting" beforeText="Hand-sculpting"
      afterIcon="injection_mold" afterText="Mold specification"
      slideIn={interpolate(frame, [40, 70], [-100, 0], { extrapolateRight: 'clamp' })}
      opacity={interpolate(frame, [40, 70, 330, 360], [0, 1, 1, 0])}
      afterScale={frame >= 120 ? spring({ frame: frame - 120, fps: 30 }) : 0}
      beforeDim={interpolate(frame, [150, 240], [1.0, 0.6], { extrapolateRight: 'clamp' })}
    />

    {/* Column 3 — Semiconductors */}
    <IndustryColumn
      x={1240} width={480}
      header="SEMICONDUCTORS"
      beforeIcon="pencil_ruler" beforeText="Hand-drawn gates"
      afterIcon="code_terminal" afterText="HDL + synthesis"
      slideIn={interpolate(frame, [60, 90], [-100, 0], { extrapolateRight: 'clamp' })}
      opacity={interpolate(frame, [60, 90, 330, 360], [0, 1, 1, 0])}
      afterScale={frame >= 120 ? spring({ frame: frame - 120, fps: 30 }) : 0}
      beforeDim={interpolate(frame, [150, 240], [1.0, 0.6], { extrapolateRight: 'clamp' })}
    />

    {/* Divider with THE SHIFT label */}
    <ShiftDivider
      y={530}
      sweepProgress={interpolate(frame, [90, 120], [0, 1], { extrapolateRight: 'clamp' })}
      opacity={interpolate(frame, [90, 110, 330, 360], [0, 1, 1, 0])}
    />

    {/* Bottom banner */}
    <Sequence from={240} durationInFrames={120}>
      <BannerText
        text="We've seen this before — we just didn't recognize it."
        position={[960, 800]}
        opacity={interpolate(frame, [0, 30], [0, 1], { extrapolateRight: 'clamp' })}
        translateY={interpolate(frame, [0, 30], [10, 0], { extrapolateRight: 'clamp' })}
        italic
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "columns": [
    {
      "industry": "TEXTILES",
      "before": { "icon": "needle_thread", "text": "Hand-darning", "color": "#F97316" },
      "after": { "icon": "factory_loom", "text": "Automated weaving", "color": "#3B82F6" }
    },
    {
      "industry": "PLASTICS",
      "before": { "icon": "hands_sculpting", "text": "Hand-sculpting", "color": "#F97316" },
      "after": { "icon": "injection_mold", "text": "Mold specification", "color": "#3B82F6" }
    },
    {
      "industry": "SEMICONDUCTORS",
      "before": { "icon": "pencil_ruler", "text": "Hand-drawn gates", "color": "#F97316" },
      "after": { "icon": "code_terminal", "text": "HDL + synthesis", "color": "#3B82F6" }
    }
  ],
  "divider_label": "THE SHIFT",
  "banner": "We've seen this before — we just didn't recognize it.",
  "total_frames": 360,
  "fps": 30
}
```

---
