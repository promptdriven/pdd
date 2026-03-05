[title:Why You're Still Darning Socks] Cold Open Title Card

# Section 0.1: Title Card — "Why You're Still Darning Socks"

**Tool:** Remotion
**Duration:** ~4s
**Timestamp:** 0:00 - 0:04

## Visual Description
A bold title card that fades in from black over the opening Veo footage. The text "Why You're Still Darning Socks" appears center-screen with a subtle scale-up animation. It holds for ~3 seconds, then fades out as the narration continues. The title sits on a semi-transparent dark scrim that ensures readability over the cinematic background.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Scrim: radial gradient from rgba(15, 23, 42, 0.7) center to rgba(15, 23, 42, 0.0) edges

### Chart/Visual Elements
- Title text: centered at (960, 400), vertically offset 37% from top
- Scrim layer: full-width band from y=280 to y=520, feathered edges

### Animation Sequence
1. **Frame 0-30 (0-1s):** Title fades in — opacity 0→1, scale 0.92→1.0. Scrim fades in with same timing.
2. **Frame 30-90 (1-3s):** Hold at full opacity. No motion.
3. **Frame 90-120 (3-4s):** Title fades out — opacity 1→0. Scrim fades out simultaneously.

### Typography
- Title: Inter Bold, 72px, white (#FFFFFF)
- Text shadow: 0 4px 16px rgba(0, 0, 0, 0.6)
- Letter spacing: -0.02em
- Line height: 1.1

### Easing
- Fade in: `easeOutCubic`
- Scale in: `easeOutCubic`
- Fade out: `easeInCubic`

## Narration Sync
> "If you use Cursor, Claude Code, or Copilot —"

Title appears at the very start and fades out before "you're getting really good at this."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  {/* Semi-transparent scrim */}
  <ScrimOverlay opacity={interpolate(frame, [0, 30, 90, 120], [0, 0.7, 0.7, 0])} />
  {/* Title text */}
  <TitleText
    text="Why You're Still Darning Socks"
    style={{
      opacity: interpolate(frame, [0, 30, 90, 120], [0, 1, 1, 0], { extrapolateRight: 'clamp' }),
      transform: `scale(${interpolate(frame, [0, 30], [0.92, 1.0], { extrapolateRight: 'clamp' })})`,
    }}
  />
</Sequence>
```

## Data Points
```json
{
  "text": "Why You're Still Darning Socks",
  "fadeInFrames": 30,
  "holdFrames": 60,
  "fadeOutFrames": 30,
  "totalFrames": 120
}
```

---
