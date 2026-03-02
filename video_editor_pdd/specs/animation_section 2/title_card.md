[title:Animation Pipeline Demo] Animation Section Title Card

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

## Animation
- Opacity: interpolate [0, 30] → [0, 1]
- Subtle scale: interpolate [0, 30] → [0.95, 1.0]
- Hold at full opacity until subtitle text begins
