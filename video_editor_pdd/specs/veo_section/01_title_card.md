[title:]

# Section 2.1: Veo Section Title Card

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:00 - 0:03

## Visual Description
A cinematic title card introducing the Veo Section. The text "VEO SECTION" materializes letter-by-letter against a dark charcoal background, accompanied by a thin horizontal light streak that sweeps across the frame. A subtle amber/gold accent glow pulses once behind the title, evoking a warm cinematic tone that previews the sunset and nature footage to come.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark charcoal (#121212) with a soft radial gradient center highlight (#2A1F0E at 35% radius)

### Chart/Visual Elements
- Title text: "VEO SECTION" — centered horizontally and vertically, warm white (#FFF8E7)
- Light streak: Horizontal line, 1px, amber (#F59E0B at 60% opacity), sweeps left-to-right across full width
- Radial glow: Soft warm pulse behind text, 500px diameter, #2A1F0E at center fading to transparent
- Subtle film-grain noise overlay at 3% opacity for cinematic texture

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Background fades in from black. Radial glow begins at 0% opacity.
2. **Frame 10-30 (0.33-1s):** Light streak sweeps from left edge to right edge across the frame.
3. **Frame 15-50 (0.5-1.67s):** Title text reveals letter-by-letter left-to-right, each letter fading from 0% to 100% opacity with 2-frame stagger.
4. **Frame 30-50 (1-1.67s):** Radial glow pulses from 0% to 80% opacity and back to 40%.
5. **Frame 50-90 (1.67-3s):** Hold — all elements static. Glow at 40% opacity, title fully visible.

### Typography
- Title: Inter Bold, 72px, #FFF8E7, letter-spacing 8px, uppercase
- No additional labels

### Easing
- Letter reveal: `easeOutCubic`
- Light streak: `linear`
- Glow pulse: `easeInOutSine`

## Narration Sync
> (No narration — title card plays before narrator begins)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <CinematicBackground grain={0.03} />
  <Sequence from={10}>
    <LightStreak color="#F59E0B" opacity={0.6} />
  </Sequence>
  <Sequence from={15}>
    <LetterRevealTitle text="VEO SECTION" staggerFrames={2} />
  </Sequence>
  <Sequence from={30}>
    <RadialGlowPulse color="#2A1F0E" maxOpacity={0.8} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "VEO SECTION",
  "accentColor": "#F59E0B",
  "backgroundColor": "#121212",
  "glowColor": "#2A1F0E"
}
```

---
