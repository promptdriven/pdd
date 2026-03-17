[Remotion]

# Section 6.7: Sock Economics Callback — Metaphor Full Circle

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 24:03 - 24:11

## Visual Description

The sock metaphor from the opening returns for one final, satisfying callback. The screen begins with a single white sock on the left, gently resting at an angle. A price tag drops in: "$0.50" in small, casual text. Then a second tag drops beside it: "$3.00 labor" — representing the cost of patching. A red strikethrough slashes the labor tag, killing the idea of repair.

The scene cross-fades to the right half of the screen: a code module block with two floating cost tags. "Regeneration: $0.02" appears in blue, tiny, almost free. "Manual Fix: $15+" appears in amber, heavy, expensive. The same red strikethrough slashes the manual fix tag. The parallel is unmistakable.

A caption fades in at the bottom center: "The economics made patching irrational." — in white, clean and definitive. This visual closes the loop on the entire video's thesis: when generation becomes cheap, maintenance becomes waste.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: none

### Chart/Visual Elements

#### Phase 1 — Sock Side (left half, x 80-900)

##### Sock Illustration
- Position: (350, 420), ~160w × 200h
- Style: minimalist line art, 3px `#E2E8F0` at 0.6 stroke, slight rotation -8°
- Fill: `#E2E8F0` at 0.05

##### Price Tag — Sock Cost
- Position: (300, 320)
- Tag shape: 80w × 36h, `#1E293B`, rounded 6px, 1px `#334155` border
- Hole + string: small circle + curved line to sock
- Text: "$0.50" — JetBrains Mono, 14px, `#E2E8F0` at 0.7

##### Price Tag — Patch Labor
- Position: (460, 320)
- Tag shape: 120w × 36h, `#1E293B`, rounded 6px, 1px `#D9944A` at 0.3 border
- Text: "$3.00 labor" — JetBrains Mono, 14px, `#D9944A`

##### Strikethrough (patch labor)
- Diagonal line across patch labor tag, 2px, `#EF4444` at 0.7
- Extends 8px beyond tag edges on each side

#### Phase 2 — Code Side (right half, x 1020-1840)

##### Code Module Block
- Position: (1380, 420), 140w × 160h
- Background: `#1E293B`, rounded 10px, 2px `#334155` border
- Icon: `</>` glyph, 32px, `#94A3B8` at 0.5, centered
- Label: "module" — Inter, 11px, `#94A3B8` at 0.4, below icon

##### Cost Tag — Regeneration
- Position: (1250, 330)
- Tag shape: 160w × 36h, `#1E293B`, rounded 6px, 1px `#4A90D9` at 0.3 border
- Text: "Regeneration: $0.02" — JetBrains Mono, 13px, `#4A90D9`

##### Cost Tag — Manual Fix
- Position: (1250, 390)
- Tag shape: 160w × 36h, `#1E293B`, rounded 6px, 1px `#D9944A` at 0.3 border
- Text: "Manual Fix: $15+" — JetBrains Mono, 13px, `#D9944A`

##### Strikethrough (manual fix)
- Diagonal line across manual fix tag, 2px, `#EF4444` at 0.7
- Extends 8px beyond tag edges

#### Caption
- Position: centered at (960, 800)
- Text: "The economics made patching irrational." — Inter, 22px, medium (500), `#E2E8F0` at 0.8
- Subtle underline: 360px, 1px, `#FBBF24` at 0.2

#### Cross-fade Divider
- Vertical divider at x=960, `#334155` at 0.15, 1px, draws during phase 2 entrance

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Sock illustration draws in with stroke animation. Gentle rotation settle.
2. **Frame 25-55 (0.83-1.83s):** Sock price tag drops in from above with slight swing. "$0.50" visible.
3. **Frame 55-85 (1.83-2.83s):** Patch labor tag drops in. "$3.00 labor" visible. Brief pause.
4. **Frame 85-100 (2.83-3.33s):** Red strikethrough slashes across patch labor tag. Tag dims to 0.3.
5. **Frame 100-130 (3.33-4.33s):** Cross-fade to right side. Divider line appears. Code module block fades in.
6. **Frame 130-155 (4.33-5.17s):** Regeneration cost tag slides in from left. "$0.02" visible — small and blue.
7. **Frame 155-175 (5.17-5.83s):** Manual fix cost tag slides in below. "$15+" visible — large and amber.
8. **Frame 175-195 (5.83-6.5s):** Red strikethrough slashes manual fix tag. Tag dims to 0.3. The parallel is complete.
9. **Frame 195-220 (6.5-7.33s):** Caption fades in at bottom. Underline draws left-to-right.
10. **Frame 220-240 (7.33-8s):** Hold on full composition. Both sides visible, both "expensive" options struck through.

### Typography
- Price tags: JetBrains Mono, 13-14px, respective colors
- Module label: Inter, 11px, `#94A3B8` at 0.4
- Caption: Inter, 22px, medium (500), `#E2E8F0` at 0.8

### Easing
- Sock draw: `easeInOut(cubic)` stroke-dashoffset over 25 frames
- Tag drop: `easeOut(bounce)` from y-40, 18 frames
- Strikethrough slash: `easeOut(cubic)` over 12 frames
- Cross-fade: `easeInOut(quad)` opacity transition over 25 frames
- Cost tag slide: `easeOut(cubic)` from x-30, 18 frames
- Caption fade: `easeOut(quad)` over 18 frames
- Underline draw: `easeInOut(cubic)` over 15 frames

## Narration Sync
> "You don't patch socks because socks got cheap. The economics made patching irrational."

Segment: `where_to_start_003`

- **24:03** ("You don't patch socks"): Sock with price tags visible, strikethrough on labor
- **24:06** ("because socks got cheap"): Cross-fade to code module side
- **24:08** ("The economics made"): Both sides visible, manual fix struck through
- **24:10** ("patching irrational"): Caption appears at bottom — the thesis restated

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Phase 1 — Sock side */}
    <Sequence from={0}>
      <StrokeDraw duration={25}>
        <SockIllustration x={350} y={420} width={160} height={200}
          strokeColor="#E2E8F0" strokeOpacity={0.6}
          strokeWidth={3} rotation={-8} />
      </StrokeDraw>
    </Sequence>

    <Sequence from={25}>
      <DropIn from={-40} duration={18} easing="easeOut(bounce)">
        <PriceTag x={300} y={320} width={80} text="$0.50"
          textColor="#E2E8F0" borderColor="#334155" />
      </DropIn>
    </Sequence>

    <Sequence from={55}>
      <DropIn from={-40} duration={18} easing="easeOut(bounce)">
        <PriceTag x={460} y={320} width={120} text="$3.00 labor"
          textColor="#D9944A" borderColor="#D9944A" />
      </DropIn>
    </Sequence>

    <Sequence from={85}>
      <Strikethrough target="patch_labor_tag" color="#EF4444"
        opacity={0.7} width={2} overshoot={8} duration={12} />
    </Sequence>

    {/* Cross-fade divider */}
    <Sequence from={100}>
      <FadeIn duration={20}>
        <Line x={960} y1={200} y2={700}
          color="#334155" opacity={0.15} width={1} />
      </FadeIn>
    </Sequence>

    {/* Phase 2 — Code side */}
    <Sequence from={100}>
      <FadeIn duration={25}>
        <ModuleBlock x={1380} y={420} width={140} height={160}
          bgColor="#1E293B" borderColor="#334155"
          icon="code" label="module" />
      </FadeIn>
    </Sequence>

    <Sequence from={130}>
      <SlideIn direction="left" distance={30} duration={18}>
        <CostTag x={1250} y={330} width={160}
          text="Regeneration: $0.02"
          textColor="#4A90D9" borderColor="#4A90D9" />
      </SlideIn>
    </Sequence>

    <Sequence from={155}>
      <SlideIn direction="left" distance={30} duration={18}>
        <CostTag x={1250} y={390} width={160}
          text="Manual Fix: $15+"
          textColor="#D9944A" borderColor="#D9944A" />
      </SlideIn>
    </Sequence>

    <Sequence from={175}>
      <Strikethrough target="manual_fix_tag" color="#EF4444"
        opacity={0.7} width={2} overshoot={8} duration={12} />
    </Sequence>

    {/* Caption */}
    <Sequence from={195}>
      <FadeIn duration={18}>
        <Text text="The economics made patching irrational."
          font="Inter" size={22} weight={500}
          color="#E2E8F0" opacity={0.8}
          x={960} y={800} align="center" />
      </FadeIn>
      <Sequence from={10}>
        <LineDraw from={[780, 825]} to={[1140, 825]}
          color="#FBBF24" opacity={0.2} width={1} duration={15} />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "metaphor_callback",
  "callbackId": "sock_economics_callback",
  "sockSide": {
    "item": "sock",
    "itemCost": "$0.50",
    "repairCost": "$3.00 labor",
    "repairStruck": true
  },
  "codeSide": {
    "item": "code module",
    "cheapOption": { "label": "Regeneration", "cost": "$0.02", "color": "#4A90D9" },
    "expensiveOption": { "label": "Manual Fix", "cost": "$15+", "color": "#D9944A", "struck": true }
  },
  "caption": "The economics made patching irrational.",
  "backgroundColor": "#0F172A",
  "narrationSegments": ["where_to_start_003"]
}
```

---
