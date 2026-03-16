[split:]

# Section 2.4: Value Migration — Crafting vs. Molding

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 9:07 - 9:21

## Visual Description
A split-screen comparison drives home where value lives in each paradigm. The LEFT half represents "Crafting": a hand-carved wooden chair sits on a pedestal, glowing with a protective golden aura — the object IS the value. When the chair breaks (cracks appear), the aura shatters and everything is lost. The RIGHT half represents "Molding": a mold cavity blueprint glows with the golden aura instead — the specification is the value. Below it, a plastic part sits dim and expendable. When the part breaks, the aura stays on the mold and a new part simply regenerates. Bottom overlay labels crystallize the message: "Lose the chair = lose everything" vs. "Lose the part = regenerate at will."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Vertical Divider:** 2px line at X=960, full height, `rgba(255,255,255,0.12)`
- **Left Panel — Crafting (X: 0-958)**
  - Header: "Crafting" — `#94A3B8`, 22px, at (240, 60)
  - Chair Object: Stylized wooden chair silhouette, 140px x 180px, centered at (480, 380), fill `#4A90D9` at 0.7 opacity
  - Value Aura: Golden glow around chair, `rgba(251,191,36,0.25)` radial gradient, radius 140px, blur 20px
  - Pedestal: Rounded rectangle 180px x 16px at Y=490, `rgba(255,255,255,0.1)`
  - Crack Lines (appear later): 3 jagged lines across the chair, `#EF4444`, 2px
  - Shatter Particles: 12 fragments radiating outward from chair center
  - Sub-label: "Value lives in the object" — `#CBD5E1`, 16px, at Y=550
  - Bottom Overlay: "Lose the chair = lose everything" — `#EF4444` at 0.8, 18px, at Y=860
- **Right Panel — Molding (X: 962-1920)**
  - Header: "Molding" — `#94A3B8`, 22px, at (1200, 60)
  - Mold Blueprint: Rectangular outline with cavity profile, 160px x 120px, centered at (1440, 320), stroke `#D9944A`, 2px
  - Value Aura: Golden glow around the MOLD (not the part), `rgba(251,191,36,0.25)` radial gradient, radius 120px, blur 20px
  - Plastic Part: Small chair silhouette below mold, 80px x 100px, at (1440, 480), fill `#4A90D9` at 0.3 opacity (dim, expendable)
  - Crack Lines on Part (appear later): 2 jagged lines, `#EF4444`, 1.5px
  - Regeneration: Part fades out, new identical part fades in (fresh, clean)
  - Sub-label: "Value lives in the specification" — `#CBD5E1`, 16px, at Y=550
  - Bottom Overlay: "Lose the part = regenerate at will" — `#2AA198` at 0.8, 18px, at Y=860

### Animation Sequence
1. **Frame 0-30 (0-1s):** Divider draws top-to-bottom. Headers and sub-labels fade in on both sides
2. **Frame 30-60 (1-2s):** Left: Chair silhouette and pedestal fade in. Aura glows around chair. Right: Mold blueprint draws in. Aura glows around mold. Dim plastic part fades in below
3. **Frame 60-90 (2-3s):** Hold — viewer absorbs the contrast of where the aura sits (object vs. specification)
4. **Frame 90-150 (3-5s):** LEFT: Cracks appear across the chair (stroke-dashoffset animation). Aura flickers. At frame 130, chair shatters into 12 fragments that fly outward and fade. Aura collapses to nothing
5. **Frame 150-180 (5-6s):** LEFT: Empty pedestal remains. Loss is total
6. **Frame 150-210 (5-7s):** RIGHT: Cracks appear on the plastic part. Part fades to 0. Mold aura stays completely stable — doesn't even flicker. After 30 frames, a fresh part fades in at the same position, clean and intact
7. **Frame 210-280 (7-9.3s):** Hold — both final states visible. Left: empty pedestal. Right: mold with fresh part
8. **Frame 280-340 (9.3-11.3s):** Bottom overlay labels slide up and fade in on both sides
9. **Frame 340-420 (11.3-14s):** Hold at final state

### Typography
- Headers: Inter, 22px, semi-bold (600), `#94A3B8`
- Sub-labels: Inter, 16px, regular (400), `#CBD5E1`
- Bottom Overlays: Inter, 18px, medium (500), respective colors at 0.8 opacity

### Easing
- Divider draw: `easeOut(cubic)`
- Chair/mold fade-in: `easeOut(quad)`
- Aura glow: `easeInOut(sine)` (subtle breathing)
- Crack draw: `easeIn(cubic)` (accelerating damage)
- Shatter fragments: `easeOut(quad)` with random angle offsets
- Aura collapse: `easeIn(cubic)` (rapid)
- Part regeneration: `easeOut(quad)`
- Bottom labels slide: `easeOut(cubic)`

## Narration Sync
> "And when there's a defect?"
> "You don't patch individual parts. You fix the mold. And that fix applies to every part you'll ever make again."
> "This is the real shift. Not 'cheaper material.' A migration of where value lives."
> "In crafting, value lives in the object. You protect the object. Losing the chair is losing everything."
> "In molding, value lives in the specification, the mold. The plastic part? Disposable. Regenerate it at will."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  {/* Divider */}
  <Sequence from={0} durationInFrames={30}>
    <VerticalDivider x={960} color="rgba(255,255,255,0.12)" />
  </Sequence>

  {/* Left Panel — Crafting */}
  <AbsoluteFill style={{ clipPath: "inset(0 50% 0 0)" }}>
    <PanelHeader text="Crafting" x={240} y={60} />
    <Sequence from={30}>
      <ChairSilhouette x={480} y={380} color="#4A90D9" />
      <ValueAura x={480} y={380} color="rgba(251,191,36,0.25)" />
      <Pedestal x={480} y={490} />
      <SubLabel text="Value lives in the object" y={550} />
    </Sequence>
    <Sequence from={90} durationInFrames={60}>
      <CrackAndShatter targetX={480} targetY={380} fragmentCount={12} />
    </Sequence>
    <Sequence from={280}>
      <OverlayLabel text="Lose the chair = lose everything" color="#EF4444" y={860} />
    </Sequence>
  </AbsoluteFill>

  {/* Right Panel — Molding */}
  <AbsoluteFill style={{ clipPath: "inset(0 0 0 50%)" }}>
    <PanelHeader text="Molding" x={1200} y={60} />
    <Sequence from={30}>
      <MoldBlueprint x={1440} y={320} color="#D9944A" />
      <ValueAura x={1440} y={320} color="rgba(251,191,36,0.25)" />
      <PlasticPart x={1440} y={480} color="#4A90D9" opacity={0.3} />
      <SubLabel text="Value lives in the specification" y={550} />
    </Sequence>
    <Sequence from={150} durationInFrames={60}>
      <CrackAndRegenerate partX={1440} partY={480} />
    </Sequence>
    <Sequence from={280}>
      <OverlayLabel text="Lose the part = regenerate at will" color="#2AA198" y={860} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "divider": {
    "x": 960,
    "color": "rgba(255,255,255,0.12)"
  },
  "leftPanel": {
    "header": "Crafting",
    "object": {
      "type": "chairSilhouette",
      "position": { "x": 480, "y": 380 },
      "size": { "width": 140, "height": 180 },
      "color": "#4A90D9"
    },
    "aura": { "color": "rgba(251,191,36,0.25)", "radius": 140, "blur": 20 },
    "subLabel": "Value lives in the object",
    "overlayLabel": "Lose the chair = lose everything",
    "overlayColor": "#EF4444",
    "shatterFragments": 12
  },
  "rightPanel": {
    "header": "Molding",
    "mold": {
      "position": { "x": 1440, "y": 320 },
      "size": { "width": 160, "height": 120 },
      "color": "#D9944A"
    },
    "part": {
      "position": { "x": 1440, "y": 480 },
      "size": { "width": 80, "height": 100 },
      "color": "#4A90D9",
      "opacity": 0.3
    },
    "aura": { "color": "rgba(251,191,36,0.25)", "radius": 120, "blur": 20 },
    "subLabel": "Value lives in the specification",
    "overlayLabel": "Lose the part = regenerate at will",
    "overlayColor": "#2AA198"
  }
}
```

---
