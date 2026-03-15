[split:]

# Section 2.3: Value Migration — Craft vs. Mold Split Screen

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 8:53 - 9:05

## Visual Description
A split-screen comparison illustrating where value lives in two paradigms. LEFT: A craftsman hand-carving a wooden chair — each cut is permanent, history accumulates in the wood. A warm golden aura surrounds the chair itself (the object holds the value). RIGHT: An injection mold with plastic flowing through it — the plastic part is unremarkable, but the mold glows with a teal aura (the specification holds the value). The plastic part dissolves and instantly regenerates, identical — proving the part is disposable while the mold is precious. Both sides use clean geometric shapes, not photorealistic illustration.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Left `#1A1408` (warm wood dark), Right `#0A1218` (cool industrial dark)
- Grid lines: None
- Vertical divider: 2px, `#FFFFFF` at 0.2 opacity, X=960

### Chart/Visual Elements
- **Left Panel — Crafting:**
  - Header: "Crafting" in `#FFFFFF`, 22px semi-bold, top-center at Y=60px
  - Chair shape: Simplified geometric chair — 4 rectangles (legs) + 1 rectangle (seat) + 1 rectangle (back), `#A0845C` (warm wood) with `#7A6543` stroke, centered at (480, 480)
  - Chisel marks: 5-6 small notch shapes along edges, `#8B7355`, accumulated over time
  - Glow aura: Radial gradient from `rgba(217, 168, 74, 0.25)` center to transparent, radius 200px, surrounding the chair shape
  - Label: "Value lives in the object" in `#D9A84A`, 18px, Y=780px
  - Sub-label: "Losing the chair is losing everything." in `#94A3B8`, 14px, Y=810px

- **Right Panel — Molding:**
  - Header: "Molding" in `#FFFFFF`, 22px semi-bold, top-center at Y=60px
  - Mold shape: Cross-section view, two trapezoidal walls, `#2AA198` at 0.4 opacity with `#2AA198` 2px stroke, centered at (1440, 380)
  - Plastic part: Rounded rectangle in cavity, `#D9944A` at 0.5 opacity, 120px wide x 200px tall
  - Glow aura: Radial gradient from `rgba(42, 161, 152, 0.25)` center to transparent, radius 200px, surrounding the MOLD (not the part)
  - Label: "Value lives in the specification" in `#2AA198`, 18px, Y=780px
  - Sub-label: "The plastic part? Disposable." in `#94A3B8`, 14px, Y=810px

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Both panels slide in — left from left edge, right from right edge. Divider appears
2. **Frame 15-30 (0.5-1.0s):** Headers "Crafting" and "Molding" fade in
3. **Frame 30-80 (1.0-2.67s):** Left: Chair shape assembles piece by piece — legs, then seat, then back. Each piece fades in with a slight scale-up. Chisel marks appear one by one. Right: Mold walls draw in. Plastic part fills cavity (amber particles coalesce)
4. **Frame 80-140 (2.67-4.67s):** Glow auras fade in. Left: golden aura surrounds the CHAIR. Right: teal aura surrounds the MOLD (not the part). The contrast in where the glow sits is the key visual beat
5. **Frame 140-180 (4.67-6.0s):** Labels fade in on both sides: "Value lives in the object" vs "Value lives in the specification"
6. **Frame 180-240 (6.0-8.0s):** Right panel: The plastic part dissolves (particles scatter outward, opacity → 0). Beat. Then a new identical part instantly materializes in the cavity (particles converge inward). The mold glow never wavers
7. **Frame 240-280 (8.0-9.33s):** Sub-labels fade in: "Losing the chair is losing everything." vs "The plastic part? Disposable."
8. **Frame 280-360 (9.33-12.0s):** Hold. Left aura pulses gently on the chair. Right part dissolves and regenerates once more (subtle loop). The disposability of the part vs. the permanence of the mold is reinforced

### Typography
- Panel Headers: Inter, 22px, semi-bold (600), `#FFFFFF`
- Value Labels: Inter, 18px, semi-bold (600), left `#D9A84A` / right `#2AA198`
- Sub-Labels: Inter, 14px, regular (400), `#94A3B8`

### Easing
- Panel slide-in: `easeOut(cubic)`
- Chair piece assembly: `easeOut(quad)` with 8-frame staggers
- Mold draw: `easeOut(cubic)`
- Glow aura fade-in: `easeOut(quad)` over 30 frames
- Part dissolve: `easeIn(quad)` (scatter)
- Part regenerate: `easeOut(back(1.1))` (converge)
- Labels: `easeOut(quad)`

## Narration Sync
> "This is the real shift. Not 'cheaper material.' A migration of where value lives."
> "In crafting, value lives in the object. You protect the object. Losing the chair is losing everything."
> "In molding, value lives in the specification — the mold. The plastic part? Disposable. Regenerate it at will."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  {/* Left Panel — Crafting */}
  <SplitPanel side="left" background="#1A1408">
    <PanelHeader text="Crafting" />
    <Sequence from={30}>
      <GeometricChair
        position={[480, 480]}
        woodColor="#A0845C"
        chiselMarks={6}
      />
    </Sequence>
    <Sequence from={80}>
      <GlowAura
        center={[480, 480]}
        radius={200}
        color="rgba(217, 168, 74, 0.25)"
        target="chair"
      />
    </Sequence>
    <Sequence from={140}>
      <ValueLabel text="Value lives in the object" color="#D9A84A" />
    </Sequence>
    <Sequence from={240}>
      <SubLabel text="Losing the chair is losing everything." />
    </Sequence>
  </SplitPanel>

  {/* Divider */}
  <VerticalDivider x={960} opacity={0.2} />

  {/* Right Panel — Molding */}
  <SplitPanel side="right" background="#0A1218">
    <PanelHeader text="Molding" />
    <Sequence from={30}>
      <MoldCrossSection wallColor="#2AA198" />
      <PlasticPart color="#D9944A" opacity={0.5} />
    </Sequence>
    <Sequence from={80}>
      <GlowAura
        center={[1440, 380]}
        radius={200}
        color="rgba(42, 161, 152, 0.25)"
        target="mold"
      />
    </Sequence>
    <Sequence from={140}>
      <ValueLabel text="Value lives in the specification" color="#2AA198" />
    </Sequence>
    <Sequence from={180}>
      <DissolveRegenerate partColor="#D9944A" cycles={2} />
    </Sequence>
    <Sequence from={240}>
      <SubLabel text="The plastic part? Disposable." />
    </Sequence>
  </SplitPanel>
</Sequence>
```

## Data Points
```json
{
  "leftPanel": {
    "title": "Crafting",
    "background": "#1A1408",
    "chairColor": "#A0845C",
    "chiselMarkColor": "#8B7355",
    "chiselMarks": 6,
    "auraColor": "rgba(217, 168, 74, 0.25)",
    "label": "Value lives in the object",
    "labelColor": "#D9A84A",
    "subLabel": "Losing the chair is losing everything."
  },
  "rightPanel": {
    "title": "Molding",
    "background": "#0A1218",
    "moldColor": "#2AA198",
    "partColor": "#D9944A",
    "partOpacity": 0.5,
    "auraColor": "rgba(42, 161, 152, 0.25)",
    "label": "Value lives in the specification",
    "labelColor": "#2AA198",
    "subLabel": "The plastic part? Disposable."
  },
  "divider": {
    "x": 960,
    "color": "#FFFFFF",
    "opacity": 0.2,
    "width": 2
  },
  "backgroundColor": "#0A0F1A"
}
```

---
