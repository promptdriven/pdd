[title:]

# Section 0.6: PDD Title Card

**Tool:** Title
**Duration:** ~1s
**Timestamp:** 0:17 - 0:18

## Visual Description
Clean title card fade-in over a dark background. The text "Prompt-Driven Development" appears centered on screen in a modern sans-serif typeface, white on near-black. The text fades in with a subtle upward drift (8px travel). Below the main title, a thin horizontal rule (80px wide, #FFFFFF30) draws itself from center outward, followed by a tagline "stop patching. start generating." in smaller, lighter type. The overall feel is minimal, confident, and slightly provocative — a thesis statement, not a product logo.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0A0A0A (near-black)
- No grid lines

### Chart/Visual Elements
- **Title text:** centered horizontally at y=480
- **Horizontal rule:** centered at y=540, 80px wide, 1px height, #FFFFFF30
- **Tagline:** centered horizontally at y=570

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Title text fades in (opacity 0 → 1) with upward drift (translateY 8px → 0px)
2. **Frame 15-25 (0.5-0.83s):** Horizontal rule draws from center outward (width 0 → 80px)
3. **Frame 20-30 (0.67-1.0s):** Tagline fades in (opacity 0 → 0.6)

### Typography
- Title: `Inter`, 56px, weight 300 (light), color #FFFFFF, letter-spacing 2px
- Tagline: `Inter`, 18px, weight 400, color #FFFFFF, opacity 0.6, letter-spacing 3px, text-transform uppercase

### Easing
- Title fade + drift: `easeOutCubic`
- Rule draw: `easeInOutQuad`
- Tagline fade: `easeOutQuad`

## Narration Sync
> (No narration — title card appears in the pause after "So why are we still patching?")

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  <AbsoluteFill style={{ background: '#0A0A0A', justifyContent: 'center', alignItems: 'center' }}>
    <Sequence from={0} durationInFrames={20}>
      <FadeInDrift direction="up" distance={8}>
        <Title text="Prompt-Driven Development" />
      </FadeInDrift>
    </Sequence>
    <Sequence from={15} durationInFrames={10}>
      <DrawRule width={80} color="#FFFFFF30" />
    </Sequence>
    <Sequence from={20} durationInFrames={10}>
      <FadeIn targetOpacity={0.6}>
        <Tagline text="stop patching. start generating." />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "title": "Prompt-Driven Development",
  "tagline": "stop patching. start generating.",
  "background": "#0A0A0A",
  "titleStyle": {
    "font": "Inter",
    "size": 56,
    "weight": 300,
    "color": "#FFFFFF",
    "letterSpacing": "2px"
  }
}
```
