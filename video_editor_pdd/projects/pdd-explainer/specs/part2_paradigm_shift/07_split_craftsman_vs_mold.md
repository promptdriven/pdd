[split:]

# Section 2.7: Split Screen — Craftsman vs. Injection Mold

**Tool:** Split
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 1:35 - 1:55

## Visual Description

A split-screen composition that persists across three narration beats, establishing the core insight: the migration of where value lives.

**LEFT PANEL:** A craftsman hand-carving a wooden chair. Each cut is permanent, history accumulating in the wood. The craftsman works carefully, deliberately — the object IS the value. A glowing amber aura gradually appears around the wooden chair itself (not the craftsman, not the tools — the object).

**RIGHT PANEL:** The injection mold with liquid plastic flowing through it. Parts eject, identical and disposable. A glowing blue aura gradually appears around the MOLD itself (not the plastic part). Then the plastic part dissolves and a new one instantly appears, identical — proving the mold holds the value, not the output.

The split holds through three segments: the "where value lives" introduction, the crafting vs. molding contrast, and the "disposable output" revelation. Both panels progress in parallel, with the aura effect building to make the point visually unmistakable.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Layout: Two 940px-wide panels with 40px center divider
- Divider: White (#FFFFFF), 2px solid line, 40% opacity
- Background behind divider: Black (#000000)

### Panel Configuration
- Left panel: clip `craftsman_carving` (full duration)
- Right panel: clip `mold_plastic_flow` (full duration)
- Aura overlay: Remotion-composited glow effect on each panel

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split screen fades in from black. Divider appears. Both panels begin simultaneously.
2. **Frame 15-120 (0.5-4s):** LEFT: Craftsman carving wooden chair, deliberate cuts. RIGHT: Injection mold operating, plastic flowing. Establishing the contrast.
3. **Frame 120-240 (4-8s):** Aura effect begins. LEFT: Warm amber glow (`#D9944A` at 0.3) appears around the wooden chair. RIGHT: Cool blue glow (`#4A90D9` at 0.3) appears around the MOLD (not the plastic part).
4. **Frame 240-360 (8-12s):** Auras intensify. LEFT: Chair glows — the object is precious. RIGHT: Mold glows — the specification is precious. The plastic part remains unglow.
5. **Frame 360-480 (12-16s):** RIGHT: The plastic part dissolves (fade to transparent). A beat. Then a new identical part fades in — proving the part is disposable, the mold is permanent.
6. **Frame 480-600 (16-20s):** Hold. The contrast is complete. Split screen holds for a beat before fade-out.

### Typography
- None within panels — the aura effect carries the visual argument.

### Easing
- Divider fade-in: `easeOut(quad)` over 15 frames
- Aura appear: `easeInOut(cubic)` over 60 frames
- Aura intensify: `easeIn(quad)` over 60 frames
- Part dissolve: `easeIn(cubic)` over 30 frames
- Part reappear: `easeOut(cubic)` over 20 frames
- Final hold: static

## Narration Sync
> "In crafting, value lives in the object. You protect the object. Losing the chair is losing everything."
> "In molding, value lives in the specification—the mold. The plastic part? Disposable. Regenerate it at will."

Segments: `part2_paradigm_shift_009`, `part2_paradigm_shift_010`

- **92.64s** (seg 009): Split screen establishes — craftsman vs. mold
- **96.0s**: Aura begins appearing — "value lives in the object"
- **102.0s**: Auras intensifying — "You protect the object"
- **108.0s**: "Losing the chair is losing everything" — chair aura bright
- **112.48s** (seg 009 ends → seg 010 begins): "value lives in the specification"
- **116.0s**: Plastic part dissolves — "The plastic part? Disposable"
- **118.0s**: New part appears — "Regenerate it at will"
- **120.06s** (seg 010 ends): Split holds, fade-out begins

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <SplitScreen dividerColor="#FFFFFF" dividerWidth={2} dividerOpacity={0.4}>
    {/* Left panel: craftsman */}
    <PanelLeft>
      <VeoClip clipId="craftsman_carving" />
      <Sequence from={120}>
        <AuraGlow
          target="object" color="#D9944A" opacity={0.3}
          buildDuration={120} easing="easeInOutCubic"
        />
      </Sequence>
    </PanelLeft>

    {/* Right panel: injection mold */}
    <PanelRight>
      <VeoClip clipId="mold_plastic_flow" />
      <Sequence from={120}>
        <AuraGlow
          target="mold" color="#4A90D9" opacity={0.3}
          buildDuration={120} easing="easeInOutCubic"
        />
      </Sequence>
      {/* Part dissolve and reappear */}
      <Sequence from={360}>
        <PartDissolveReappear
          dissolveDuration={30} reappearDelay={30}
          reappearDuration={20}
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
  "divider": { "color": "#FFFFFF", "width": 2, "opacity": 0.4 },
  "panels": {
    "left": {
      "clips": ["craftsman_carving"],
      "label": "Craftsman — value in the object",
      "aura": { "color": "#D9944A", "target": "object" }
    },
    "right": {
      "clips": ["mold_plastic_flow"],
      "label": "Mold — value in the specification",
      "aura": { "color": "#4A90D9", "target": "mold" },
      "partDissolve": true
    }
  },
  "narrationSegments": ["part2_paradigm_shift_009", "part2_paradigm_shift_010"],
  "durationSeconds": 20.0
}
```

---
