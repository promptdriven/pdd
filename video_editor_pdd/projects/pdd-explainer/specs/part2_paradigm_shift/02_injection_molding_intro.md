[Remotion]

# Section 2.2: Injection Molding — The Manufacturing Parallel

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 8:33 - 8:53

## Visual Description
A geometric, stylized visualization of injection molding as a metaphor for specification-driven development. The scene opens with a cross-sectional view of an injection mold — two precision walls forming a cavity. Liquid material (represented as flowing particles) injects into the cavity and fills the shape. A counter ticks up as identical parts eject in sequence: 1, 10, 100, 10,000. Then a defect appears in a molded part (red highlight). Instead of patching the part, the scene transitions to an engineer adjusting the mold wall itself. New parts eject — all perfect. The defective part is simply discarded (fades away). This establishes the core metaphor: fix the mold, not the part.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark charcoal `#0A0F1A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Mold Cross-Section:** Centered, 600px wide x 400px tall
  - Left wall: Trapezoidal shape, `#2AA198` (teal) fill at 0.3 opacity, `#2AA198` 2px stroke
  - Right wall: Mirror of left, same colors
  - Cavity: Negative space between walls, ~200px wide
  - Injection nozzle: Small funnel shape at top center, `#2AA198` at 0.5 opacity
- **Flowing Material:** Particle system — 60-80 small circles (3-5px radius), `#D9944A` (amber) at varying opacities (0.4-0.8), flowing downward from nozzle into cavity
- **Molded Part:** Rounded rectangle matching cavity shape, `#D9944A` at 0.6 opacity, 180px wide x 280px tall
- **Part Counter:** Top-right corner, `#FFFFFF`, JetBrains Mono 28px — "1" → "10" → "100" → "10,000"
- **Defect Highlight:** Red circle/irregular shape on one molded part, `#EF4444` at 0.5 opacity, 20px radius, with pulsing glow
- **Engineer Adjustment:** Small wrench/tool icon (`#FFFFFF` at 0.6 opacity) touching the mold wall. Wall segment shifts 4px inward (subtle geometry change). Blue flash on adjusted area `rgba(74,144,217,0.3)`
- **Discarded Part:** Defective part fades to 0.1 opacity and drifts 30px downward

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Mold cross-section draws in — left wall, right wall, nozzle. Clean geometric construction
2. **Frame 40-100 (1.33-3.33s):** Particles flow from nozzle into cavity. They accumulate, filling the shape from bottom up. Material solidifies — particles merge into solid molded-part shape
3. **Frame 100-130 (3.33-4.33s):** Mold opens (walls slide apart 40px). Part ejects rightward. Counter: "1". Mold closes
4. **Frame 130-220 (4.33-7.33s):** Rapid cycle — fill, open, eject, close. Parts eject in sequence. Counter accelerates: "10"... "100"... "10,000". Parts stack/fan out on the right side
5. **Frame 220-280 (7.33-9.33s):** Focus on one ejected part. Red defect highlight pulses on its surface. "DEFECT" label fades in beside it
6. **Frame 280-360 (9.33-12.0s):** Scene shift — instead of touching the defective part, a tool icon approaches the mold wall. The wall segment adjusts (subtle 4px inward shift). Blue flash on adjusted area. The mold wall now has a slightly different profile
7. **Frame 360-440 (12.0-14.67s):** New cycle — fill, open, eject. New parts emerge perfect (green checkmark appears briefly on each). Three parts eject, all clean
8. **Frame 440-520 (14.67-17.33s):** Defective part fades away (opacity → 0.1, drifts down). New perfect parts glow briefly. The contrast: fix the mold, discard the part
9. **Frame 520-600 (17.33-20.0s):** Hold. All elements at rest. Mold glows with subtle teal aura. Parts are present but unremarkable. Text fades in bottom-center: "Fix the mold. Not the part."

### Typography
- Counter: JetBrains Mono, 28px, bold (700), `#FFFFFF`, opacity 0.8
- "DEFECT" label: Inter, 16px, semi-bold (600), `#EF4444`
- Summary text: Inter, 24px, semi-bold (600), `#FFFFFF`, opacity 0.9

### Easing
- Mold draw: `easeOut(cubic)`
- Particle flow: `linear` with slight random jitter
- Part eject: `easeOut(quad)`
- Counter increment: `easeOut(back(1.2))`
- Defect pulse: `easeInOut(sin)` repeating
- Tool approach: `easeInOut(cubic)`
- Wall adjustment: `easeOut(quad)`
- Part fade-out: `easeIn(quad)`
- Summary text: `easeOut(quad)`

## Narration Sync
> "Consider injection molding. Before it existed, you crafted individual objects. After it? You designed molds."
> "Make the mold once, produce unlimited identical parts. Refine the mold once, every future part improves automatically."
> "And when there's a defect? You don't patch individual parts. You fix the mold. And that fix applies to every part you'll ever make again."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  {/* Mold Construction */}
  <Sequence from={0} durationInFrames={40}>
    <MoldCrossSection
      width={600}
      height={400}
      wallColor="#2AA198"
      wallOpacity={0.3}
    />
  </Sequence>

  {/* First Fill Cycle */}
  <Sequence from={40} durationInFrames={60}>
    <ParticleFlow
      particleCount={70}
      color="#D9944A"
      nozzleY={200}
      cavityBounds={{ left: 380, right: 580, bottom: 680 }}
    />
  </Sequence>

  {/* Ejection Cycles */}
  <Sequence from={100} durationInFrames={120}>
    <EjectionCycle
      cycleCount={4}
      counterValues={[1, 10, 100, 10000]}
    />
  </Sequence>

  {/* Defect Discovery */}
  <Sequence from={220} durationInFrames={60}>
    <DefectHighlight
      position={[1100, 500]}
      color="#EF4444"
      label="DEFECT"
    />
  </Sequence>

  {/* Mold Adjustment */}
  <Sequence from={280} durationInFrames={80}>
    <MoldAdjustment
      toolIcon="wrench"
      adjustmentDelta={4}
      flashColor="rgba(74,144,217,0.3)"
    />
  </Sequence>

  {/* Perfect Parts */}
  <Sequence from={360} durationInFrames={80}>
    <EjectionCycle cycleCount={3} showCheckmarks={true} />
  </Sequence>

  {/* Defect Discard + Summary */}
  <Sequence from={440} durationInFrames={80}>
    <FadeOut target="defectivePart" />
  </Sequence>
  <Sequence from={520}>
    <SummaryText text="Fix the mold. Not the part." />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "mold": {
    "width": 600,
    "height": 400,
    "wallColor": "#2AA198",
    "wallStroke": 2,
    "cavityWidth": 200
  },
  "material": {
    "particleCount": 70,
    "color": "#D9944A",
    "particleRadius": [3, 5]
  },
  "ejection": {
    "counterValues": [1, 10, 100, 10000],
    "partColor": "#D9944A",
    "partOpacity": 0.6
  },
  "defect": {
    "color": "#EF4444",
    "radius": 20
  },
  "adjustment": {
    "delta": 4,
    "flashColor": "rgba(74, 144, 217, 0.3)"
  },
  "summary": "Fix the mold. Not the part.",
  "backgroundColor": "#0A0F1A"
}
```

---
