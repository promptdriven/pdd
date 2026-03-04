[title:The Mold Has Three Parts] Section Title Card

## Remotion Overlay Spec
- Type: text overlay on Veo background
- Appear: frame 0, fade-in over 30 frames
- Hold: ~3 seconds
- Disappear: fade-out over 20 frames

## Typography
- Font: Inter Bold (or system sans-serif fallback)
- Size: 72px
- Color: white (#FFFFFF)
- Shadow: 0 2px 12px rgba(0,0,0,0.6)
- Position: center screen, vertically offset 40% from top
- Letter spacing: -0.02em

## Subtitle
- Text: "Test Capital · Prompt Capital · Grounding Capital"
- Font: Inter Regular
- Size: 28px
- Color: white 70% opacity
- Position: centered, 12px below main title

## Animation
- Opacity: interpolate [0, 30] → [0, 1]
- Subtle scale: interpolate [0, 30] → [0.95, 1.0]
- Subtitle fades in 10 frames after title (staggered)
- Hold at full opacity until narration begins
