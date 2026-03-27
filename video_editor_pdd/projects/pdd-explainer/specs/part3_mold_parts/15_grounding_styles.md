[Remotion]

# Section 3.15: Grounding Styles — OOP vs. Functional

**Tool:** Remotion
**Duration:** ~26s (780 frames @ 30fps)
**Timestamp:** 4:57 - 5:23

## Visual Description

A panel showing material properties with the "Grounding" label at the top. Three material streams flow from left to right, each labeled:
- "OOP" — deep blue (`#4A90D9`), angular texture blocks
- "Functional" — warm amber (`#D9944A`), smooth flowing shapes
- "Your Team's Style" — teal (`#4AD9A0`), organic pattern

Then the visualization transitions to show the same prompt and same tests producing two different code outputs depending on grounding context:

**Path A:** Grounding from OOP codebase → generates classes with methods. A code panel shows `class UserParser:` with methods.

**Path B:** Grounding from functional codebase → generates pure functions with composition. A code panel shows `def parse_user_id(raw: str) -> Optional[str]:` with function composition.

Both outputs are valid — they pass the same walls. The grounding determines the style/flavor, not the correctness.

Then: a successful generation glows and flows into a "Grounding Database" icon. An arrow shows the (prompt, code) pair being stored in cloud storage. Future generations pull from this database. After `pdd fix` succeeds, the knowledge feeds back.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Phase 1: Material Streams
- Three horizontal streams, y-spaced 80px apart, centered vertically
- Each stream: 600px wide animated gradient bar, 40px tall, rounded ends
- Labels: Inter, 16px, semi-bold (600), matching color
- "Grounding" header: Inter, 24px, bold (700), `#4AD9A0`, centered at top

#### Phase 2: OOP vs Functional Split
- Two code panels, 580px × 350px each, side by side with 40px gap
- Path A (left): `#1E1E2E` fill, `#4A90D9` border, header "OOP Grounding"
- Path B (right): `#1E1E2E` fill, `#D9944A` border, header "Functional Grounding"
- Code: JetBrains Mono, 11px, syntax highlighted
- Both share: "Same prompt. Same tests." label above, Inter, 14px, `#94A3B8`

#### Phase 3: Grounding Database Feedback
- Database icon: cylinder shape, 80px × 60px, `#4AD9A0` fill at 0.2, `#4AD9A0` border
- Label: "Grounding Database" — Inter, 14px, semi-bold (600), `#4AD9A0`
- Arrow from successful code → database icon, `#4AD9A0` at 0.4, animated flow
- Arrow from database → future generation, dashed, `#4AD9A0` at 0.3
- Terminal note: `pdd fix` → "(prompt, code) → cloud" — JetBrains Mono, 11px, `#A6E3A1`

### Animation Sequence
1. **Frame 0-30 (0-1s):** "Grounding" header fades in.
2. **Frame 30-120 (1-4s):** Three material streams animate from left to right, each with distinct motion character.
3. **Frame 120-180 (4-6s):** Streams cross-fade into the OOP vs Functional split. "Same prompt. Same tests." label appears.
4. **Frame 180-270 (6-9s):** Path A code panel: OOP-style Python code types in.
5. **Frame 270-360 (9-12s):** Path B code panel: functional-style Python code types in.
6. **Frame 360-420 (12-14s):** Both panels glow — both valid. Walls visible at edges confirming both pass.
7. **Frame 420-480 (14-16s):** Transition: right panel code glows brighter (selected generation).
8. **Frame 480-600 (16-20s):** Arrow animation from glowing code to Grounding Database icon. "(prompt, code)" pair flows along arrow. Database pulses on receipt.
9. **Frame 600-720 (20-24s):** Dashed arrow from database to a "Future Generation" placeholder. The feedback loop is complete.
10. **Frame 720-780 (24-26s):** Hold. The grounding accumulation cycle is clear.

### Typography
- Header: Inter, 24px, bold (700), `#4AD9A0`
- Stream labels: Inter, 16px, semi-bold (600)
- Code: JetBrains Mono, 11px, syntax colors
- Panel headers: Inter, 14px, semi-bold (600)
- Database label: Inter, 14px, semi-bold (600), `#4AD9A0`

### Easing
- Stream animation: `easeInOut(sine)` flowing motion
- Code type-in: linear, 1 frame per character
- Glow: `easeOut(quad)` over 20 frames
- Arrow flow: `easeInOut(cubic)` over 40 frames
- Database pulse: `easeInOut(sine)` single cycle over 15 frames

## Narration Sync
> "Third: grounding. This determines the properties of what fills the mold. Grounding is learned from your past generations. When you successfully generate and fix code, that knowledge feeds back into the system. Your style. Your patterns. Your team's conventions. Grounding captures all of it and applies it automatically to future generations."

Segment: `part3_mold_parts_019`

- **297.60s** (seg 019): "Third: grounding" — material streams begin
- **302.0s**: "properties of what fills the mold" — streams flowing
- **306.0s**: OOP vs Functional split — "Grounding is learned from your past generations"
- **312.0s**: Code typing in — "When you successfully generate and fix code"
- **316.0s**: Feedback arrow — "that knowledge feeds back into the system"
- **320.0s**: Database stores — "Your style. Your patterns."
- **323.20s** (seg 019 ends): Feedback loop complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={780}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Phase 1: Material streams */}
    <Sequence from={0} durationInFrames={180}>
      <FadeIn duration={15}>
        <Text text="Grounding" font="Inter" size={24}
          weight={700} color="#4AD9A0" x={960} y={120} align="center" />
      </FadeIn>

      {MATERIAL_STREAMS.map((stream, i) => (
        <Sequence key={i} from={30 + i * 20}>
          <MaterialStream
            color={stream.color} label={stream.label}
            y={300 + i * 80} width={600}
            animationStyle={stream.style}
          />
        </Sequence>
      ))}
    </Sequence>

    {/* Phase 2: OOP vs Functional */}
    <Sequence from={120}>
      <CrossFade duration={30}>
        <Text text="Same prompt. Same tests." font="Inter" size={14}
          color="#94A3B8" x={960} y={200} align="center" />

        <CodePanel x={170} y={260} width={580} height={350}
          header="OOP Grounding" headerColor="#4A90D9"
          borderColor="#4A90D9" code={OOP_CODE}
          typeInStart={60} />

        <CodePanel x={810} y={260} width={580} height={350}
          header="Functional Grounding" headerColor="#D9944A"
          borderColor="#D9944A" code={FUNCTIONAL_CODE}
          typeInStart={150} />
      </CrossFade>
    </Sequence>

    {/* Phase 3: Database feedback */}
    <Sequence from={480}>
      <FlowArrow
        from={[1090, 450]} to={[960, 750]}
        color="#4AD9A0" duration={40}
        label="(prompt, code)"
      />
      <Sequence from={40}>
        <FadeIn duration={15}>
          <DatabaseIcon x={960} y={800}
            color="#4AD9A0" label="Grounding Database" />
        </FadeIn>
      </Sequence>
    </Sequence>

    <Sequence from={600}>
      <DashedArrow
        from={[960, 830]} to={[960, 920]}
        color="#4AD9A0" opacity={0.3}
        label="Future Generations"
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "grounding_styles",
  "materialStreams": [
    { "label": "OOP", "color": "#4A90D9", "style": "angular" },
    { "label": "Functional", "color": "#D9944A", "style": "smooth" },
    { "label": "Your Team's Style", "color": "#4AD9A0", "style": "organic" }
  ],
  "codeComparison": {
    "pathA": { "style": "OOP", "borderColor": "#4A90D9" },
    "pathB": { "style": "Functional", "borderColor": "#D9944A" }
  },
  "feedbackLoop": {
    "database": "Grounding Database",
    "stores": "(prompt, code) pair"
  },
  "narrationSegments": ["part3_mold_parts_019"],
  "durationSeconds": 26.0
}
```

---
