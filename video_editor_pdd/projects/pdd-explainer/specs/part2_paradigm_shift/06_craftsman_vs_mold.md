[split:]

# Section 2.6: Craftsman vs Mold — Where Value Lives

**Tool:** Split
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 1:24 - 1:44

## Visual Description

A vertical split screen showing the fundamental contrast between crafting and molding. **LEFT:** A craftsman hand-carving a wooden chair. Each cut is permanent, history accumulating in the wood. A warm glowing aura surrounds the chair itself — the object IS the value. **RIGHT:** An injection mold with plastic flowing through it. A glowing aura surrounds the MOLD, not the plastic part. The plastic part dissolves; a new one instantly appears, identical.

The split holds across multiple narration beats: the initial comparison, the "where value lives" insight, and the disposability demonstration. The aura effect is the visual punch — it makes the abstract concept of "where value lives" immediately tangible.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black behind both panels)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Left Panel — Craftsman + Wooden Chair
- **Phase 1 (0-8s):** Veo clip `craftsman_carving` — warm-lit close-up of a craftsman hand-carving a wooden chair. Wood shavings curl. Each cut is deliberate, permanent.
- **Phase 2 (8-14s):** A glowing aura appears around the wooden chair. The aura is warm gold `#FFB347` at 0.3, soft glow, 40px radius. Label fades in: "Value lives in the object" — Inter, 14px, `#FFB347` at 0.7, positioned below the chair.
- **Phase 3 (14-20s):** The chair remains, aura holding. The permanence is the point — you can't undo those cuts.

#### Right Panel — Injection Mold
- **Phase 1 (0-8s):** Veo clip `mold_producing_parts` — close-up of an injection mold producing a plastic part. Steel mold visible, plastic flowing.
- **Phase 2 (8-14s):** A glowing aura appears around the MOLD (not the plastic part). The aura is cool blue `#4A90D9` at 0.3, soft glow, 40px radius. Label: "Value lives in the specification" — Inter, 14px, `#4A90D9` at 0.7, positioned below the mold.
- **Phase 3 (14-20s):** The plastic part dissolves (fade out with particle effect). A new identical part instantly appears (fade in). The mold's aura holds steady throughout — the mold is permanent, the parts are disposable.

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split line fades in from center outward.
2. **Frame 15-240 (0.5-8s):** Both panels active. LEFT: craftsman carving. RIGHT: mold producing. Narration: "In crafting, value lives in the object..."
3. **Frame 240-330 (8-11s):** Aura effects appear simultaneously on both sides. LEFT: warm gold aura on chair. RIGHT: cool blue aura on mold.
4. **Frame 330-420 (11-14s):** Labels fade in. The contrast is stark — value in different places.
5. **Frame 420-480 (14-16s):** RIGHT panel: plastic part begins dissolving. Particles drift away.
6. **Frame 480-540 (16-18s):** RIGHT panel: new identical part materializes. Mold aura never wavered.
7. **Frame 540-600 (18-20s):** Hold. Both auras visible. The fundamental difference is clear.

### Typography
- Left label: Inter, 14px, semi-bold (600), `#FFB347` at 0.7
- Right label: Inter, 14px, semi-bold (600), `#4A90D9` at 0.7

### Easing
- Split line fade: `easeOut(quad)` over 15 frames
- Aura appear: `easeOut(cubic)` over 30 frames — soft bloom
- Label fade-in: `easeOut(quad)` over 20 frames
- Part dissolve: `easeIn(quad)` over 40 frames
- Part reappear: `easeOut(cubic)` over 20 frames
- Aura pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "This is the real shift. Not 'cheaper material.' A migration of where value lives."
> "In crafting, value lives in the object. You protect the object. Losing the chair is losing everything."
> "In molding, value lives in the specification — the mold. The plastic part? Disposable. Regenerate it at will."

Segments: `part2_paradigm_shift_010`, `part2_paradigm_shift_011`, `part2_paradigm_shift_012`

- **1:24** ("real shift"): Split screen appears, both working
- **1:34** ("value lives in the object"): Warm aura on chair, label appears
- **1:42** ("plastic part? Disposable"): Part dissolves, new one appears. Mold aura holds.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Craftsman */}
    <Panel x={0} width={958}>
      <Sequence from={0} durationInFrames={240}>
        <VeoClip clipId="craftsman_carving"
          src="/clips/craftsman_carving.mp4" fit="cover" />
      </Sequence>

      {/* Aura on the chair */}
      <Sequence from={240}>
        <GlowAura
          target="center" color="#FFB347"
          opacity={0.3} radius={40}
          fadeIn={30} pulse={60} />
        <Sequence from={90}>
          <FadeIn duration={20}>
            <Text text="Value lives in the object"
              font="Inter" size={14} weight={600}
              color="#FFB347" opacity={0.7}
              x={479} y={880} align="center" />
          </FadeIn>
        </Sequence>
      </Sequence>
    </Panel>

    {/* Split divider */}
    <Sequence from={0}>
      <FadeIn duration={15}>
        <SplitLine x={960} color="#334155" opacity={0.15} width={2} />
      </FadeIn>
    </Sequence>

    {/* Right panel — Injection Mold */}
    <Panel x={962} width={958}>
      <Sequence from={0} durationInFrames={240}>
        <VeoClip clipId="mold_producing_parts"
          src="/clips/mold_producing_parts.mp4" fit="cover" />
      </Sequence>

      {/* Aura on the mold (not the part) */}
      <Sequence from={240}>
        <GlowAura
          target="mold_area" color="#4A90D9"
          opacity={0.3} radius={40}
          fadeIn={30} pulse={60} />
        <Sequence from={90}>
          <FadeIn duration={20}>
            <Text text="Value lives in the specification"
              font="Inter" size={14} weight={600}
              color="#4A90D9" opacity={0.7}
              x={479} y={880} align="center" />
          </FadeIn>
        </Sequence>
      </Sequence>

      {/* Part dissolve and reappear */}
      <Sequence from={420}>
        <ParticleDissolve target="plastic_part"
          duration={40} particleColor="#4A90D9" />
      </Sequence>
      <Sequence from={480}>
        <FadeIn duration={20}>
          <PlasticPart position="center" />
        </FadeIn>
      </Sequence>
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
    "content": "veo_clip_with_aura",
    "clipId": "craftsman_carving",
    "aura": { "color": "#FFB347", "target": "wooden_chair" },
    "label": "Value lives in the object",
    "thematicRole": "crafting_value_in_object"
  },
  "rightPanel": {
    "content": "veo_clip_with_aura",
    "clipId": "mold_producing_parts",
    "aura": { "color": "#4A90D9", "target": "injection_mold" },
    "label": "Value lives in the specification",
    "partDissolves": true,
    "thematicRole": "molding_value_in_spec"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["part2_paradigm_shift_010", "part2_paradigm_shift_011", "part2_paradigm_shift_012"]
}
```

---
