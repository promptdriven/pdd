[title:]

# Section 0.6: PDD Title Card

**Tool:** Remotion
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 0:18 - 0:21

## Visual Description

The "So why are we still patching?" text dissolves. From the center of the screen, the title "Prompt-Driven Development" fades in — large, clean, authoritative. The text appears over a very faint version of the regenerated code from 04, visible at ~5% opacity as a texture.

A thin horizontal rule animates outward from center, left and right simultaneously, 400px total width. Below the rule, a subtle tagline: "the mold is what matters" in smaller italic text, fading in 0.5s after the title.

The color palette is restrained: white text on deep charcoal with the faintest blue glow behind the title, referencing the project's primary prompt color #4A90D9.

This is the end of the cold open. It holds for 1.5 seconds of stillness before cutting to the next section.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0A0F1A (deep charcoal)
- Code texture: regenerated code from 04 at 5% opacity, blurred 4px

### Chart/Visual Elements

**Title Text**
- "Prompt-Driven Development"
- Position: centered at (960, 480)
- Subtle blue glow: box-shadow 0 0 80px rgba(74,144,217,0.12)

**Horizontal Rule**
- Position: y=530, centered
- Animates from center outward: width 0 → 400px
- Color: rgba(255,255,255,0.3), height 1px

**Tagline**
- "the mold is what matters"
- Position: centered at (960, 570)

**Background Glow**
- Radial gradient: rgba(74,144,217,0.06) → transparent
- Center: (960, 480), radius 500px

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Previous text ("So why are we still patching?") dissolves — opacity 1 → 0, slight scale 1.0 → 0.98.
2. **Frame 10-30 (0.33-1.0s):** Background glow fades in. Title "Prompt-Driven Development" fades in with slight scale-up 0.95 → 1.0.
3. **Frame 30-42 (1.0-1.4s):** Horizontal rule animates from center outward, width 0 → 400px.
4. **Frame 42-55 (1.4-1.83s):** Tagline "the mold is what matters" fades in. Opacity 0 → 0.7.
5. **Frame 55-90 (1.83-3.0s):** Hold. Everything static. Clean beat of stillness.

### Typography
- Title: `Inter`, 64px, weight 700, #FFFFFF, letter-spacing 1px
- Tagline: `Inter`, 20px, weight 400, italic, #FFFFFF, opacity 0.7, letter-spacing 2px

### Easing
- Previous text dissolve: `easeIn(quad)`
- Title fade-in: `easeOut(cubic)`
- Title scale: `easeOut(back(1.1))`
- Horizontal rule expand: `easeInOut(cubic)`
- Tagline fade-in: `easeOut(quad)`

## Narration Sync
> (No narration — title card over silence / ambient tone. Follows "So why are we still patching?" with a pause.)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <Background color="#0A0F1A">
    <BlurredCodeTexture opacity={0.05} blur={4} />
    <RadialGlow center={[960, 480]} radius={500} color="rgba(74,144,217,0.06)" />
  </Background>
  <Sequence from={0} durationInFrames={10}>
    <FadeOut>
      <PreviousQuestionText />
    </FadeOut>
  </Sequence>
  <Sequence from={10} durationInFrames={20}>
    <FadeIn scale={{ from: 0.95, to: 1.0 }}>
      <TitleText text="Prompt-Driven Development" />
    </FadeIn>
  </Sequence>
  <Sequence from={30} durationInFrames={12}>
    <HorizontalRule y={530} maxWidth={400} color="rgba(255,255,255,0.3)" />
  </Sequence>
  <Sequence from={42} durationInFrames={13}>
    <FadeIn>
      <Tagline text="the mold is what matters" />
    </FadeIn>
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "background": {
    "color": "#0A0F1A",
    "codeTexture": { "opacity": 0.05, "blur": 4 }
  },
  "glow": {
    "color": "rgba(74,144,217,0.06)",
    "center": [960, 480],
    "radius": 500
  },
  "title": {
    "text": "Prompt-Driven Development",
    "font": "Inter",
    "fontSize": 64,
    "fontWeight": 700,
    "color": "#FFFFFF",
    "letterSpacing": 1,
    "position": [960, 480],
    "glowColor": "rgba(74,144,217,0.12)",
    "glowBlur": 80,
    "scaleFrom": 0.95,
    "scaleTo": 1.0
  },
  "horizontalRule": {
    "y": 530,
    "maxWidth": 400,
    "color": "rgba(255,255,255,0.3)",
    "height": 1
  },
  "tagline": {
    "text": "the mold is what matters",
    "font": "Inter",
    "fontSize": 20,
    "fontWeight": 400,
    "fontStyle": "italic",
    "color": "#FFFFFF",
    "opacity": 0.7,
    "letterSpacing": 2,
    "position": [960, 570]
  },
  "narrationSegments": [],
  "narrationTimingSeconds": { "start": 17.54, "end": 20.0 }
}
```

---
