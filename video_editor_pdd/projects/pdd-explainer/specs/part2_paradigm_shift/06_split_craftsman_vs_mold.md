[split:]

# Section 2.6: Split Screen — Craftsman vs. Injection Mold

**Tool:** Split
**Duration:** ~25s (750 frames @ 30fps)
**Timestamp:** 1:26 - 1:51

## Visual Description
A split-screen composition that persists across three narration beats, illustrating the core paradigm shift: where value lives.

**LEFT PANEL:** A craftsman hand-carving a wooden chair in a warm workshop. Each cut is permanent, each stroke adds history to the wood. The lighting is warm amber — intimate, personal. The aura effect appears around the wooden chair itself (the object), highlighting that in crafting, value lives in the artifact.

**RIGHT PANEL:** The injection molding machine producing plastic parts. The lighting is cool industrial blue. When the aura effect appears, it surrounds the MOLD (the specification), not the plastic part — showing that in molding, value lives in the specification. A plastic part dissolves and instantly regenerates, identical, demonstrating disposability.

The split holds through three segments: the "real shift" declaration, the crafting/value explanation, and the molding/value explanation. The aura effects appear sequentially — LEFT first (crafting value = object), then RIGHT (molding value = mold).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Layout: Two 940px-wide panels with 40px center divider
- Divider: White (#FFFFFF), 2px solid line, 60% opacity
- Background behind divider: Black (#000000)

### Panel Configuration
- Left panel: clip `craftsman_carving` — warm amber tones
- Right panel: clip `mold_producing_parts` — cool industrial blues
- Aura overlays rendered as animated Remotion layers on top of each panel

### Aura Effect
- LEFT aura: Golden glow (`#F59E0B` at 0.15) surrounding the wooden chair, 30px blur, pulsing
- RIGHT aura: Blue-steel glow (`#4A90D9` at 0.15) surrounding the mold (not the part), 30px blur, pulsing
- LEFT aura appears first (frame 240), RIGHT aura appears second (frame 480)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Split screen establishes. Both panels show their scenes. Divider fades in.
2. **Frame 30-240 (1-8s):** Both panels play. LEFT: craftsman carving with deliberate strokes. RIGHT: mold pressing parts, steady rhythm. No auras yet.
3. **Frame 240-360 (8-12s):** LEFT aura appears — golden glow surrounds the wooden chair. RIGHT stays neutral. "Value lives in the object."
4. **Frame 360-480 (12-16s):** LEFT aura holds. RIGHT aura appears — blue glow surrounds the MOLD, not the plastic part. "Value lives in the specification."
5. **Frame 480-600 (16-20s):** Both auras visible. On the RIGHT, a plastic part dissolves (opacity → 0 over 15 frames) and a new identical part instantly appears (opacity 0 → 1 over 5 frames). "Disposable. Regenerate it at will."
6. **Frame 600-750 (20-25s):** Hold. Both auras pulse gently. Split holds until hard cut to 1980s lab.

### Typography
- None within panels — narration carries the meaning. Aura effects provide visual labeling.

### Easing
- Aura fade-in: `easeOut(cubic)` over 30 frames
- Aura pulse: `easeInOut(sine)` on 45-frame cycle
- Part dissolve: `easeIn(quad)` over 15 frames
- Part regenerate: `easeOut(quad)` over 5 frames
- Divider fade-in: `easeOut(quad)` over 15 frames

## Narration Sync
> "This is the real shift. Not 'cheaper material.' A migration of where value lives."
> "In crafting, value lives in the object. You protect the object. Losing the chair is losing everything."
> "In molding, value lives in the specification — the mold. The plastic part? Disposable. Regenerate it at will."

Segments: `part2_paradigm_shift_010`, `part2_paradigm_shift_011`, `part2_paradigm_shift_012`

- **1:26** (85.56s): Split screen establishes — "This is the real shift"
- **1:34** (93.64s): LEFT aura appears — "In crafting, value lives in the object"
- **1:42** (102.10s): RIGHT aura appears — "In molding, value lives in the specification"
- **1:50** (110.30s): Part dissolves/regenerates — "Regenerate it at will"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={750}>
  <SplitScreen dividerColor="#FFFFFF" dividerWidth={2} dividerOpacity={0.6}>
    {/* Left panel: craftsman */}
    <PanelLeft>
      <VeoClip clipId="craftsman_carving" />
      <Sequence from={240}>
        <FadeIn duration={30}>
          <AuraGlow
            target="chair" color="#F59E0B" opacity={0.15}
            blurRadius={30} pulseFrames={45}
          />
        </FadeIn>
      </Sequence>
    </PanelLeft>

    {/* Right panel: mold */}
    <PanelRight>
      <VeoClip clipId="mold_producing_parts" />
      <Sequence from={360}>
        <FadeIn duration={30}>
          <AuraGlow
            target="mold" color="#4A90D9" opacity={0.15}
            blurRadius={30} pulseFrames={45}
          />
        </FadeIn>
      </Sequence>
      {/* Part dissolve + regenerate */}
      <Sequence from={480}>
        <PartDissolveRegenerate
          dissolveFrames={15} regenerateFrames={5}
          partColor="#D9944A"
        />
      </Sequence>
    </PanelRight>
  </SplitScreen>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_50_50",
  "divider": { "color": "#FFFFFF", "width": 2, "opacity": 0.6 },
  "panels": {
    "left": {
      "clips": ["craftsman_carving"],
      "aura": { "color": "#F59E0B", "target": "chair", "appearsAt": 8.0 },
      "label": "Value in the object"
    },
    "right": {
      "clips": ["mold_producing_parts"],
      "aura": { "color": "#4A90D9", "target": "mold", "appearsAt": 12.0 },
      "label": "Value in the specification"
    }
  },
  "narrationSegments": ["part2_paradigm_shift_010", "part2_paradigm_shift_011", "part2_paradigm_shift_012"],
  "durationSeconds": 25.0
}
```

---
