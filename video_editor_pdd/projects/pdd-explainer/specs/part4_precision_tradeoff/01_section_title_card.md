[title:]

# Section 4.1: The Precision Tradeoff — Section Title Card

**Tool:** Title
**Duration:** ~7s (199 frames @ 30fps)
**Timestamp:** 0:00 - 0:07

## Visual Description

A section title card introducing the precision tradeoff concept. "THE PRECISION" appears first in large bold weight, then "TRADEOFF" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost illustration sits at low opacity — on the left, a stylized 3D printer nozzle tracing a precise path, and on the right, a mold outline with flowing liquid. Both at very low opacity, previewing the central metaphor. The 3D printer side is drawn with precise dotted coordinate lines; the mold side has smooth flowing curves. Background is deep navy-black, consistent with Parts 1-3.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "THE PRECISION" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "TRADEOFF" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 240px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 4" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (dual illustration)
- 3D printer nozzle (left): stylized triangular nozzle at (380, 540), dotted line path below it, `#60A5FA` at 0.04, 2px stroke
- Coordinate grid (left): 5×5 grid of dots below nozzle at (300-460, 480-640), `#60A5FA` at 0.03
- Mold outline (right): rectangular mold shape at (1540, 540), `#D9944A` at 0.04, 2px stroke
- Flow curves (right): 3 wavy curves inside mold representing liquid, `#A78BFA` at 0.03

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 4" label fades in. Ghost illustrations draw with stroke-dashoffset.
3. **Frame 40-60 (1.33-2s):** "THE PRECISION" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "TRADEOFF" fades in with 10px upward slide.
6. **Frame 90-140 (3-4.67s):** Ghost printer nozzle pulses blue, then ghost mold pulses amber. Sequential emphasis.
7. **Frame 140-199 (4.67-6.63s):** Hold. Subtle overall pulse on both ghost illustrations.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "TRADEOFF" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost illustration draw: `easeInOut(cubic)` over 30 frames
- Region pulses: `easeInOut(sine)` on 30-frame intervals
- Hold pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "Let's talk about precision, because there's a subtle tradeoff that changes how you think about prompts."

Segment: `part4_precision_tradeoff_001`

- **0:00** ("Let's talk about precision"): Title card begins fade-in
- **1.33s** ("precision"): "THE PRECISION" typing on screen
- **2.33s** ("tradeoff"): "TRADEOFF" revealed
- **4.67s** ("changes how you think"): Ghost illustrations pulsing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={199}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost 3D printer illustration */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <PrinterNozzle cx={380} cy={540} color="#60A5FA" opacity={0.04} strokeWidth={2} />
        <CoordinateGrid x={300} y={480} cols={5} rows={5} color="#60A5FA" opacity={0.03} />
      </StrokeDraw>
    </Sequence>

    {/* Ghost mold illustration */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <MoldOutline cx={1540} cy={540} color="#D9944A" opacity={0.04} strokeWidth={2} />
        <FlowCurves cx={1540} cy={540} color="#A78BFA" opacity={0.03} />
      </StrokeDraw>
    </Sequence>

    {/* Section label */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="PART 4" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: THE PRECISION */}
    <Sequence from={40}>
      <TypeWriter text="THE PRECISION" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={2} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[840, 505]} to={[1080, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: TRADEOFF */}
    <Sequence from={70}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="TRADEOFF" font="Inter" size={72}
            weight={700} color="#E2E8F0"
            x={975} y={545} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Sequential ghost pulses */}
    <Sequence from={90}>
      <RegionPulse region="printer" color="#60A5FA" startFrame={0} duration={25} />
      <RegionPulse region="mold" color="#D9944A" startFrame={25} duration={25} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 4,
  "sectionLabel": "PART 4",
  "titleLine1": "THE PRECISION",
  "titleLine2": "TRADEOFF",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "printer_nozzle", "color": "#60A5FA", "side": "left" },
    { "shape": "coordinate_grid", "color": "#60A5FA", "side": "left" },
    { "shape": "mold_outline", "color": "#D9944A", "side": "right" },
    { "shape": "flow_curves", "color": "#A78BFA", "side": "right" }
  ],
  "narrationSegments": ["part4_precision_tradeoff_001"]
}
```

---
