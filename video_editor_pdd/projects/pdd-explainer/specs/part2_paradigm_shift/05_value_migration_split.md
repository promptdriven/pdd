[split:]

# Section 2.5: Value Migration Split — Crafting vs Molding

**Tool:** Split
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 9:02 - 9:18

## Visual Description

A vertical split screen contrasts two fundamentally different models of where value lives. LEFT panel (labeled "CRAFTING") shows a craftsman hand-carving a wooden chair — each cut permanent, history accumulating in the object. A warm glowing aura surrounds the chair itself, pulsing gently, indicating that the object holds the value. RIGHT panel (labeled "MOLDING") shows an injection mold with plastic flowing through it. The glowing aura surrounds the MOLD, not the plastic part — value lives in the specification.

The key moment: on the right side, the plastic part dissolves and a new identical one instantly regenerates. The aura around the mold never flickers. On the left side, if the chair were to dissolve, the aura would die — losing the object means losing everything.

Below each panel, a label summarizes: LEFT: "Value lives in the object" / RIGHT: "Value lives in the specification."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x=960, color `#334155` at 0.25

### Chart/Visual Elements

#### Panel Headers
- LEFT: "CRAFTING" — Inter, 14px, semi-bold (600), `#C4956A` at 0.5, letter-spacing 2px, centered at y: 40
- RIGHT: "MOLDING" — Inter, 14px, semi-bold (600), `#D9944A` at 0.5, letter-spacing 2px, centered at y: 40

#### Left Panel — Crafting (x: 0 to x: 958)
- Background: `#0F172A`
- **Wooden chair:** Simplified vector illustration, warm wood tones
  - Body: `#8B6D45` with wood grain texture lines at 0.1
  - Position: centered at (480, 450), ~300x400px
  - Style: clean but organic, hand-crafted feel
- **Chisel/tool marks:** Small slash marks accumulating on the chair as it's "carved"
  - `#6B5233` at 0.3, 1px lines, appearing sequentially
- **Value aura (on the OBJECT):**
  - Glow: 40px Gaussian blur around the chair silhouette
  - Color: `#C4956A` at 0.12, pulsing between 0.08 and 0.15
  - The glow surrounds the chair, not the tools
- **History labels:** Small text appearing near the chair as cuts accumulate
  - "cut 1", "cut 2"... "cut 47" — JetBrains Mono, 8px, `#C4956A` at 0.2
  - Stacking, showing accumulated history
- **Summary label:** "Value lives in the object" — Inter, 13px, `#C4956A` at 0.6, bottom center at y: 980

#### Right Panel — Molding (x: 962 to x: 1920)
- Background: `#0A0F1A`
- **Injection mold:** Simplified cross-section, 300x400px, centered at (480, 350)
  - Walls: `#D9944A` at 0.5, 3px stroke
  - Cavity: `#1E293B` at 0.3
- **Plastic part:** Simplified shape matching cavity, positioned below mold at (480, 650)
  - Color: `#94A3B8` at 0.4
  - Labeled "disposable" — Inter, 9px, `#64748B` at 0.3
- **Value aura (on the MOLD):**
  - Glow: 40px Gaussian blur around the mold (not the plastic part)
  - Color: `#D9944A` at 0.12, pulsing between 0.08 and 0.15
  - Conspicuously NOT on the plastic part
- **Regeneration effect:** Plastic part dissolves (particles scatter), then a new identical one fades in
  - Dissolve: opacity → 0 with particle effect, `#94A3B8`
  - Regenerate: opacity 0 → 0.4, 15 frames
- **Summary label:** "Value lives in the specification" — Inter, 13px, `#D9944A` at 0.6, bottom center at y: 980

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split line draws. Panel headers fade in.
2. **Frame 20-80 (0.67-2.67s):** LEFT: Chair outline draws itself. First chisel marks appear, accumulating. RIGHT: Mold cross-section draws itself.
3. **Frame 80-160 (2.67-5.33s):** LEFT: More marks accumulate. History labels stack up ("cut 1"... "cut 12"). The chair gains character. RIGHT: Plastic flows into mold, a part forms and ejects below.
4. **Frame 160-240 (5.33-8s):** LEFT: Value aura begins glowing around the chair. Warm, protective. RIGHT: Value aura begins glowing around the MOLD. The plastic part sits below, conspicuously un-glowing.
5. **Frame 240-320 (8-10.67s):** RIGHT: The plastic part dissolves — particles scatter, opacity fades. The mold's aura never flickers. A new identical part fades in. The mold is what matters.
6. **Frame 320-400 (10.67-13.33s):** Both panels hold. Auras pulse. LEFT aura on the object; RIGHT aura on the mold. The contrast is the argument.
7. **Frame 400-440 (13.33-14.67s):** Summary labels appear below each panel.
8. **Frame 440-480 (14.67-16s):** Hold on the contrast. Both auras breathe.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors, letter-spacing 2px
- History labels: JetBrains Mono, 8px, `#C4956A` at 0.2
- "disposable": Inter, 9px, `#64748B` at 0.3
- Summary labels: Inter, 13px, respective colors at 0.6

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Chair outline draw: `easeInOut(cubic)` over 40 frames
- Chisel marks: `easeOut(quad)` stagger, 5 frames apart
- Aura pulse: `easeInOut(sine)` on 40-frame cycle
- Part dissolve: `easeIn(quad)` over 20 frames
- Part regenerate: `easeOut(quad)` over 15 frames
- Summary label fade: `easeOut(quad)` over 20 frames

## Narration Sync
> "This is the real shift. Not 'cheaper material.' A migration of where value lives."
> "In crafting, value lives in the object. You protect the object. Losing the chair is losing everything."
> "In molding, value lives in the specification — the mold. The plastic part? Disposable. Regenerate it at will."

Segment: `part2_005`

- **9:02** ("This is the real shift"): Split screen appears, both panels drawing
- **9:06** ("A migration of where value lives"): Auras begin glowing
- **9:10** ("In crafting, value lives in the object"): LEFT aura pulses brighter
- **9:14** ("The plastic part? Disposable"): RIGHT part dissolves and regenerates
- **9:17** ("Regenerate it at will"): Both summary labels visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Crafting */}
    <Panel x={0} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
        <PanelHeader text="CRAFTING" color="#C4956A"
          opacity={0.5} letterSpacing={2} y={40} />

        <WoodenChair position={[480, 450]} size={[300, 400]}
          bodyColor="#8B6D45" grainOpacity={0.1}
          drawDuration={40} />

        <ChiselMarks position={[480, 450]}
          count={47} stagger={5}
          color="#6B5233" opacity={0.3} />

        <HistoryLabels
          prefix="cut" count={12}
          font="JetBrains Mono" size={8}
          color="#C4956A" opacity={0.2}
          stackPosition={[750, 300]} />

        <Sequence from={160}>
          <ValueAura target="chair" center={[480, 450]}
            radius={40} color="#C4956A"
            baseOpacity={0.12} pulseRange={[0.08, 0.15]}
            pulsePeriod={40} />
        </Sequence>

        <SummaryLabel text="Value lives in the object"
          color="#C4956A" opacity={0.6} y={980}
          appearAt={400} />
      </AbsoluteFill>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.25}
      drawDuration={15} />

    {/* Right panel — Molding */}
    <Panel x={962} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
        <PanelHeader text="MOLDING" color="#D9944A"
          opacity={0.5} letterSpacing={2} y={40} />

        <MoldCrossSection
          center={[480, 350]} width={300} height={400}
          wallColor="#D9944A" wallOpacity={0.5} wallWidth={3}
          cavityColor="#1E293B" cavityOpacity={0.3}
          drawDuration={40} />

        <PlasticPart position={[480, 650]}
          color="#94A3B8" opacity={0.4}
          label="disposable" labelColor="#64748B" />

        <Sequence from={160}>
          <ValueAura target="mold" center={[480, 350]}
            radius={40} color="#D9944A"
            baseOpacity={0.12} pulseRange={[0.08, 0.15]}
            pulsePeriod={40} />
        </Sequence>

        {/* Part dissolve and regenerate */}
        <Sequence from={240}>
          <ParticleDissolve position={[480, 650]}
            color="#94A3B8" duration={20} />
          <Sequence from={25}>
            <FadeIn duration={15}>
              <PlasticPart position={[480, 650]}
                color="#94A3B8" opacity={0.4} />
            </FadeIn>
          </Sequence>
        </Sequence>

        <SummaryLabel text="Value lives in the specification"
          color="#D9944A" opacity={0.6} y={980}
          appearAt={400} />
      </AbsoluteFill>
    </Panel>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_split",
  "splitPosition": 960,
  "leftPanel": {
    "label": "CRAFTING",
    "concept": "Value lives in the object — history accumulates, loss is permanent",
    "summaryLabel": "Value lives in the object",
    "auraTarget": "object",
    "auraColor": "#C4956A",
    "background": "#0F172A"
  },
  "rightPanel": {
    "label": "MOLDING",
    "concept": "Value lives in the specification — parts are disposable, regenerated at will",
    "summaryLabel": "Value lives in the specification",
    "auraTarget": "mold",
    "auraColor": "#D9944A",
    "partDissolveAndRegenerate": true,
    "background": "#0A0F1A"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["part2_005"]
}
```

---
