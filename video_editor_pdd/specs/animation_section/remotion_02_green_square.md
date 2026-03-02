[Remotion] Green Square — Transform and Slide

## Overlay Spec
- Type: animated shape morph
- Trigger: synced to Shot 2 start (~5s)
- Duration: 5s
- Position: center → right third

## Shape Morph
- Start: circle, 200px diameter, blue (#3B82F6)
- End: square, 180px, green (#22C55E), border-radius 8px
- Interpolation: borderRadius [100, 40, 8] over 45 frames
- Color: interpolate fill (#3B82F6 → #22C55E) over 45 frames

## Slide Animation
- Delay: begins after morph completes (~1.5s into shot)
- Motion: translateX from center (0) to +300px over 60 frames (ease-in-out)
- Shadow follows: 0 0 24px rgba(34, 197, 94, 0.4)

## Styling
- Shadow: transitions from blue glow to green glow in sync with color morph
- No stroke throughout
