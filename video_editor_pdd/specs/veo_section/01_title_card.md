[title:]

# Section 2.1: Veo Section Title Card

**Tool:** Remotion
**Duration:** ~2s
**Timestamp:** 0:00 - 0:02

## Visual Description
A cinematic title card fades in against a deep teal-black gradient background. The section title "Veo Section" appears in large white sans-serif type, centered vertically. Below the title, a thin golden horizontal rule draws itself outward from center. A subtle film-grain texture overlays the background, evoking a cinematic aesthetic distinct from the previous animation-focused section. Faint warm bokeh circles drift slowly across the background.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep teal-black gradient (#0A1A1F top → #0F2027 bottom)
- Grid lines: none

### Chart/Visual Elements
- Title text: "Veo Section" — centered at (960, 460), white (#F8FAFC)
- Horizontal rule: 350px wide, 2px tall, centered at (960, 520), warm gold (#D4A574)
- Bokeh circles: 20 circles (r=6-18px), random positions, warm tones (#D4A57415, #F59E0B10), drifting diagonally at 0.4px/frame
- Film grain overlay: full-screen noise texture at 4% opacity

### Animation Sequence
1. **Frame 0-12 (0-0.4s):** Background gradient fades from black. Bokeh circles begin drifting. Film grain appears.
2. **Frame 12-32 (0.4-1.1s):** Title text fades in with slight upward translate (-25px → 0px). Opacity 0→1.
3. **Frame 22-42 (0.7-1.4s):** Golden horizontal rule draws outward from center (scaleX 0→1).
4. **Frame 42-60 (1.4-2.0s):** Hold. All elements at full opacity.

### Typography
- Title: Inter Bold, 64px, off-white (#F8FAFC)
- Subtitle: none

### Easing
- Title fade-in: `easeOutCubic`
- Rule draw: `easeInOutQuad`
- Bokeh drift: `linear`

## Narration Sync
> (No narration — title card plays before narration begins)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill style={{
    background: "linear-gradient(180deg, #0A1A1F 0%, #0F2027 100%)"
  }}>
    <FilmGrainOverlay opacity={0.04} />
    <BokehField count={20} colors={["#D4A574", "#F59E0B"]} />
    <Sequence from={12}>
      <FadeIn duration={20}>
        <TitleText text="Veo Section" font="Inter Bold" size={64} color="#F8FAFC" />
      </FadeIn>
    </Sequence>
    <Sequence from={22}>
      <DrawRule width={350} color="#D4A574" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "title": "Veo Section",
  "backgroundColor": ["#0A1A1F", "#0F2027"],
  "accentColor": "#D4A574",
  "bokehCount": 20
}
```

---
