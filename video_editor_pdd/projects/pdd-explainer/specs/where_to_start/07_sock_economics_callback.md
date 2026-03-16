[Remotion]

# Section 6.7: Sock Economics Callback — Price Tag Drop

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 23:08 - 23:16

## Visual Description
The sock metaphor returns for its final callback, tying the entire video together. A single sock is centered on screen — the same stylized knit-texture sock from the cold open. Below it, a price tag dangles on a string showing "$0.50." A second price tag drops in from above showing the cost of patching: "$3.00 labor" — struck through in red. The absurdity is immediate: why patch a fifty-cent sock with three dollars of labor? The sock then cross-fades into a code module icon, and the price tags become "Regeneration: $0.02" vs. "Manual Fix: $15+", delivering the parallel to software. This is the emotional punctuation that makes the economics visceral.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Sock Illustration:** Centered at (960, 380), 180px tall
  - Stylized sock outline: `#D9944A` at 0.5 opacity, 2px stroke, knit-texture cross-hatch fill at 0.08 opacity
  - Heel and toe darker: `#D9944A` at 0.15 fill
  - Subtle wear mark on toe: dashed line, `#EF4444` at 0.2 opacity (the "hole" being patched)
- **Price Tag — Sock Cost (right of sock):**
  - Position: (1140, 360)
  - Tag shape: Rounded rectangle 120x50px, `#FBBF24` at 0.15 fill, `#FBBF24` at 0.3 stroke
  - String: Curved line from tag to sock, `rgba(255,255,255,0.15)`, 1px
  - Text: "$0.50" — `#FBBF24`, 20px, JetBrains Mono, bold
- **Price Tag — Patch Cost (above sock):**
  - Position: (780, 200), drops down to (780, 360)
  - Tag shape: Same style, `#EF4444` at 0.15 fill, `#EF4444` at 0.3 stroke
  - Text: "$3.00 labor" — `#EF4444`, 20px, JetBrains Mono
  - Strikethrough: Red line through the text after it settles — `#EF4444` at 0.6, 2px
- **Cross-fade to Code Module (second phase):**
  - Sock morphs into a code module block (rounded rectangle with `</>` icon)
  - Price tags morph:
    - Sock cost tag → "Regeneration: $0.02" — `#4A90D9` fill accent
    - Patch cost tag → "Manual Fix: $15+" — `#EF4444` fill accent, with strikethrough
- **Bottom Caption:** "The economics made patching irrational." — `#FFFFFF` at 0.7 opacity, 22px, Inter, centered at Y=700

### Animation Sequence
1. **Frame 0-30 (0-1s):** Sock illustration fades in from center with scale (0.9→1.0). Knit texture draws in
2. **Frame 30-60 (1-2s):** Sock cost tag swings in from right (pendulum motion on string), settling at rest. "$0.50" is visible
3. **Frame 60-100 (2-3.33s):** Patch cost tag drops in from above (Y: -50→360) with gravity easing. Settles with a slight bounce. "$3.00 labor" visible
4. **Frame 100-130 (3.33-4.33s):** Strikethrough line draws through "$3.00 labor" from left to right. A brief red pulse on the tag
5. **Frame 130-180 (4.33-6.0s):** Cross-fade: sock outline morphs into code module block (vertices interpolate). Price tags morph their text simultaneously. Colors shift — amber→blue for the "cheap" tag, red stays red for the "expensive" tag
6. **Frame 180-210 (6.0-7.0s):** Caption "The economics made patching irrational." fades in at Y=700
7. **Frame 210-240 (7.0-8.0s):** Hold. Regeneration tag glows subtly (blue breathing, 0.02 opacity oscillation)

### Typography
- Price Tag Text: JetBrains Mono, 20px, bold (700), respective tag colors
- Caption: Inter, 22px, regular (400), `#FFFFFF` at 0.7 opacity
- Module Icon Text: JetBrains Mono, 16px, regular, `#4A90D9` at 0.4 opacity

### Easing
- Sock fade/scale: `easeOut(cubic)`
- Tag swing: `spring({ damping: 10, stiffness: 80 })` (pendulum)
- Tag drop: `easeIn(quad)` for fall, `spring({ damping: 14, stiffness: 120 })` for bounce
- Strikethrough draw: `easeInOut(cubic)`
- Cross-fade morph: `easeInOut(cubic)` (vertex interpolation)
- Caption fade: `easeOut(quad)`

## Narration Sync
> "You don't patch socks because socks got cheap. The economics made patching irrational."

Segment: `where_to_start_003` (26.24s – 32.08s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  {/* Sock Illustration */}
  <Sequence from={0} durationInFrames={30}>
    <SockIllustration
      x={960}
      y={380}
      color="#D9944A"
      height={180}
    />
  </Sequence>

  {/* Price Tag: Sock Cost */}
  <Sequence from={30} durationInFrames={30}>
    <PriceTag
      text="$0.50"
      x={1140}
      y={360}
      color="#FBBF24"
      animation="swing"
    />
  </Sequence>

  {/* Price Tag: Patch Cost (drops in) */}
  <Sequence from={60} durationInFrames={40}>
    <PriceTag
      text="$3.00 labor"
      x={780}
      y={360}
      color="#EF4444"
      animation="drop"
      startY={-50}
    />
  </Sequence>

  {/* Strikethrough */}
  <Sequence from={100} durationInFrames={30}>
    <Strikethrough
      targetTag="patchCost"
      color="#EF4444"
      width={2}
    />
  </Sequence>

  {/* Cross-fade: Sock → Code Module */}
  <Sequence from={130} durationInFrames={50}>
    <MorphTransition
      from={<SockIllustration />}
      to={<CodeModuleBlock />}
    />
    <TagMorph
      from={{ text: "$0.50", color: "#FBBF24" }}
      to={{ text: "Regeneration: $0.02", color: "#4A90D9" }}
    />
    <TagMorph
      from={{ text: "$3.00 labor", color: "#EF4444" }}
      to={{ text: "Manual Fix: $15+", color: "#EF4444" }}
    />
  </Sequence>

  {/* Caption */}
  <Sequence from={180} durationInFrames={30}>
    <Caption
      text="The economics made patching irrational."
      y={700}
      fontSize={22}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "sock": {
    "x": 960,
    "y": 380,
    "height": 180,
    "color": "#D9944A",
    "wearMark": { "color": "#EF4444", "opacity": 0.2 }
  },
  "priceTags": {
    "sockCost": {
      "text": "$0.50",
      "color": "#FBBF24",
      "x": 1140,
      "y": 360
    },
    "patchCost": {
      "text": "$3.00 labor",
      "color": "#EF4444",
      "x": 780,
      "y": 360,
      "strikethrough": true
    }
  },
  "codeMorph": {
    "regenerationCost": "$0.02",
    "manualFixCost": "$15+",
    "regenerationColor": "#4A90D9",
    "manualFixColor": "#EF4444"
  },
  "caption": {
    "text": "The economics made patching irrational.",
    "y": 700
  }
}
```

---
