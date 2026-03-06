[Remotion] Call-to-Action Card with Project Branding

# Section 6.6: CTA Card — Call to Action

**Tool:** Remotion
**Duration:** ~6s
**Timestamp:** 0:17 - 0:23

## Visual Description
A clean, authoritative call-to-action card that fades in over the final Veo background. The card is centered on screen with the PDD logo mark at top, followed by the tagline "Prompt-Driven Development" in white. Below, a subtle divider line in amber separates the tagline from the CTA text: "Start building with PDD" in a slightly smaller weight. At the bottom, a URL "pdd.dev" renders in vibrant blue as a clear action point. The entire card sits on a semi-transparent dark backing that gently pulses with a warm ambient glow. The card fades in element by element, holds, then fades to black — the final image the viewer sees.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay initially, fading to solid black at end
- Card: centered, 700px x 500px, at (610, 290) to (1310, 790)

### Chart/Visual Elements
- Card backing: rgba(15, 23, 42, 0.92) with backdrop-filter blur(16px), border-radius 20px
- Card border: 1px solid rgba(245, 158, 11, 0.2)
- Ambient glow: subtle pulsing box-shadow, 0 0 60px rgba(59, 130, 246, 0.1)
- Logo mark: PDD icon, 64px, centered at top of card, #3B82F6
- Tagline: "Prompt-Driven Development" — centered below logo
- Divider: horizontal line, 120px, centered, #F59E0B at 50% opacity
- CTA text: "Start building with PDD" — centered below divider
- URL: "pdd.dev" — centered at bottom, with subtle underline
- Final fade: entire frame fades to solid black (#000000)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card backing fades in — opacity 0→1.
2. **Frame 10-30 (0.33-1s):** Logo mark fades in — opacity 0→1, scale 0.85→1.0.
3. **Frame 25-42 (0.83-1.4s):** Tagline fades in — opacity 0→1, translateY 10→0.
4. **Frame 38-50 (1.27-1.67s):** Divider line expands from center — width 0→120px.
5. **Frame 45-62 (1.5-2.07s):** CTA text fades in — opacity 0→1.
6. **Frame 58-75 (1.93-2.5s):** URL "pdd.dev" fades in — opacity 0→1, with blue glow pulse.
7. **Frame 75-150 (2.5-5s):** Hold. All elements visible. Ambient glow pulses gently (opacity oscillates 0.08-0.15 on a 60-frame cycle).
8. **Frame 150-180 (5-6s):** Entire frame fades to black — opacity 1→0 for card, background color #000000 opacity 0→1.

### Typography
- Tagline: Inter Bold, 36px, #FFFFFF, letter-spacing -0.01em
- CTA text: Inter Medium, 24px, #CBD5E1
- URL: Inter SemiBold, 28px, #3B82F6, letter-spacing 0.02em
- URL underline: 2px, #3B82F6 at 40% opacity
- Text shadow on all: 0 2px 12px rgba(0, 0, 0, 0.5)

### Easing
- Card fade: `easeOutCubic`
- Logo scale: `easeOutBack`
- Tagline slide: `easeOutQuad`
- Divider expand: `easeInOutCubic`
- URL fade: `easeOutQuad`
- Glow pulse: `sinusoidal` (smooth oscillation)
- Final fade to black: `easeInCubic`

## Narration Sync
> (Silence / music swell)

No narration during the CTA card. Music builds to a final swell and resolves. The silence lets the visual CTA speak for itself.

## Code Structure (Remotion)
```typescript
<Sequence from={CTA_START} durationInFrames={180}>
  {/* Final black fade layer (behind card, fades in at end) */}
  <AbsoluteFill style={{
    backgroundColor: '#000000',
    opacity: interpolate(frame, [150, 180], [0, 1], { extrapolateLeft: 'clamp' }),
  }} />

  {/* Card backing */}
  <AbsoluteFill style={{
    display: 'flex',
    justifyContent: 'center',
    alignItems: 'center',
    opacity: interpolate(frame, [0, 20, 150, 180], [0, 1, 1, 0]),
  }}>
    <CTACard blur={16} bgColor="rgba(15, 23, 42, 0.92)">
      {/* Logo */}
      <PDDLogo
        size={64}
        color="#3B82F6"
        style={{
          opacity: interpolate(frame, [10, 30], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
          transform: `scale(${interpolate(frame, [10, 30], [0.85, 1.0], { extrapolateRight: 'clamp' })})`,
        }}
      />

      {/* Tagline */}
      <Text style={{
        opacity: interpolate(frame, [25, 42], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        transform: `translateY(${interpolate(frame, [25, 42], [10, 0], { extrapolateRight: 'clamp' })}px)`,
        color: '#FFFFFF',
        fontSize: 36,
        fontWeight: 'bold',
      }}>
        Prompt-Driven Development
      </Text>

      {/* Divider */}
      <HorizontalRule
        width={interpolate(frame, [38, 50], [0, 120], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })}
        color="#F59E0B"
        opacity={0.5}
      />

      {/* CTA */}
      <Text style={{
        opacity: interpolate(frame, [45, 62], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        color: '#CBD5E1',
        fontSize: 24,
      }}>
        Start building with PDD
      </Text>

      {/* URL */}
      <Text style={{
        opacity: interpolate(frame, [58, 75], [0, 1], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }),
        color: '#3B82F6',
        fontSize: 28,
        fontWeight: 600,
        textDecoration: 'underline',
      }}>
        pdd.dev
      </Text>
    </CTACard>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "logo": "PDD",
  "tagline": "Prompt-Driven Development",
  "cta": "Start building with PDD",
  "url": "pdd.dev",
  "accentColor": "#F59E0B",
  "brandColor": "#3B82F6",
  "card_position": {"x": 610, "y": 290, "width": 700, "height": 500},
  "totalFrames": 180,
  "fps": 30
}
```

---
