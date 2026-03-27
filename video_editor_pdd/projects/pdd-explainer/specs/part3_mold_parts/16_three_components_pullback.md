[Remotion]

# Section 3.16: Three Components Pullback — Complete Pipeline

**Tool:** Remotion
**Duration:** ~9s (270 frames @ 30fps)
**Timestamp:** 5:24 - 5:32

## Visual Description

Pull back to see all three components working together as a unified system. The mold cross-section returns, now fully annotated:

1. **Prompt** (amber, nozzle) flows in from the top
2. **Grounding** (teal, cavity material properties) passes through the cavity as a colored fill
3. **Test Walls** (blue, walls) constrain the output
4. **Code** emerges from the bottom of the mold — the final output

An animated flow shows the full pipeline: Prompt → passes through grounding → fills the mold → constrained by test walls → code emerges. The flow is continuous, showing the system as a single process.

Labels appear alongside the flow:
- "Intent" (at prompt entry)
- "Style" (at grounding region)
- "Correctness" (at walls)
- "Output" (at code exit)

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Complete Mold (fully annotated)
- Outer shell: `#334155` stroke, 3px
- Nozzle: `#D9944A` glow at 0.4
- Walls: `#4A90D9` glow at 0.4
- Cavity: `#4AD9A0` at 0.1 fill

#### Flow Animation
- Continuous particle/stream flow from nozzle → through cavity → out bottom
- Entry: amber particles (`#D9944A`) representing prompt intent
- Mid-cavity: particles gain teal tint (`#4AD9A0`) as grounding applies
- Wall contacts: blue sparks (`#4A90D9`) where flow meets walls
- Exit: clean cyan stream (`#38BDF8`) emerges as code

#### Flow Labels
- "Intent" — Inter, 14px, semi-bold (600), `#D9944A`, near nozzle
- "Style" — Inter, 14px, semi-bold (600), `#4AD9A0`, mid-cavity
- "Correctness" — Inter, 14px, semi-bold (600), `#4A90D9`, near walls
- "Output" — Inter, 14px, semi-bold (600), `#38BDF8`, at exit

### Animation Sequence
1. **Frame 0-30 (0-1s):** Full mold fades in with all three regions visible. Camera at wide angle.
2. **Frame 30-60 (1-2s):** Flow begins: amber particles enter from nozzle. "Intent" label.
3. **Frame 60-90 (2-3s):** Particles pass through grounding region, gaining teal tint. "Style" label.
4. **Frame 90-120 (3-4s):** Flow meets walls. Blue sparks. "Correctness" label.
5. **Frame 120-180 (4-6s):** Clean stream exits bottom. "Output" label. Full pipeline visible.
6. **Frame 180-270 (6-9s):** Hold. Continuous flow cycling through the complete system. All labels visible.

### Typography
- Flow labels: Inter, 14px, semi-bold (600), color matches component
- Component labels: Inter, 12px, `#64748B` (inherited from earlier)

### Easing
- Mold fade-in: `easeOut(quad)` over 20 frames
- Particle flow: linear continuous
- Label fade-in: `easeOut(quad)` over 15 frames each
- Wall sparks: `easeOut(expo)` per spark

## Narration Sync
> "Prompt plus tests plus grounding. Intent plus constraints plus style. Together, they form a complete specification."

Segment: `part3_mold_parts_020`

- **323.64s** (seg 020): Full mold appears — "Prompt plus tests plus grounding"
- **326.0s**: Flow animating — "Intent plus constraints plus style"
- **330.0s**: Complete pipeline — "they form a complete specification"
- **332.34s** (seg 020 ends): Hold on full system

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={270}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Full mold with all regions */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <MoldCrossSection
          wallsOpacity={0.4} nozzleOpacity={0.4} cavityOpacity={0.1}
          wallColor="#4A90D9" nozzleColor="#D9944A" cavityColor="#4AD9A0"
        />
      </FadeIn>
    </Sequence>

    {/* Continuous flow animation */}
    <Sequence from={30}>
      <ParticleFlow
        path={FLOW_PATH}
        stages={[
          { region: "nozzle", color: "#D9944A" },
          { region: "cavity", color: "#4AD9A0" },
          { region: "walls", color: "#4A90D9", sparks: true },
          { region: "exit", color: "#38BDF8" }
        ]}
        particleCount={20}
        cycleFrames={60}
      />
    </Sequence>

    {/* Flow labels */}
    {FLOW_LABELS.map((label, i) => (
      <Sequence key={i} from={30 + i * 30}>
        <FadeIn duration={15}>
          <Text text={label.text} color={label.color}
            font="Inter" size={14} weight={600}
            x={label.x} y={label.y} />
        </FadeIn>
      </Sequence>
    ))}
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "pipeline_pullback",
  "stages": [
    { "component": "Prompt", "encodes": "Intent", "color": "#D9944A" },
    { "component": "Grounding", "encodes": "Style", "color": "#4AD9A0" },
    { "component": "Tests", "encodes": "Correctness", "color": "#4A90D9" },
    { "component": "Code", "encodes": "Output", "color": "#38BDF8" }
  ],
  "narrationSegments": ["part3_mold_parts_020"],
  "durationSeconds": 9.0
}
```

---
