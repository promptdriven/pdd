# Section 6.7: Fade to Black -- Title Card

**Tool:** Remotion
**Duration:** ~5 seconds
**Timestamp:** 21:25 - 21:30

## Visual Description

Fade to black. A title card appears: "Prompt-Driven Development" with a URL below. Beneath that, subtle and small: `uv tool install pdd-cli`. This is not advertising -- it is a quiet invitation. The install command is there for those who want it, not pushed on anyone. The video ends with stillness.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Fades from Dark (#1a1a2e) to Pure Black (#000000)

### Animation Elements

1. **Fade to Black**
   - Previous scene (6.6) fades out completely
   - Black fills the frame
   - Duration: ~1.5 seconds

2. **Title Text: "Prompt-Driven Development"**
   - Centered horizontally, positioned at ~40% from top
   - Font: Clean sans-serif (Inter, Helvetica Neue, or similar)
   - Size: 48px
   - Color: White (#FFFFFF) at 90% opacity
   - Weight: 600 (semi-bold)
   - Letter-spacing: 2px
   - No glow, no animation beyond fade-in -- clean and authoritative

3. **URL Line**
   - Below title, centered
   - Font: Monospace, 18px
   - Color: White at 50% opacity
   - Text: `github.com/pdd-dev/pdd` (or appropriate URL)
   - Subtle, informational

4. **Install Command**
   - Below URL, centered
   - Font: Monospace, 16px
   - Color: White at 30% opacity -- deliberately understated
   - Text: `uv tool install pdd-cli`
   - Preceded by subtle `$` prompt character
   - This is the quietest element on screen -- there for the curious, not the casual

### Visual Design

```
┌──────────────────────────────────────────────────────────────┐
│                                                              │
│                         (pure black)                         │
│                                                              │
│                                                              │
│                                                              │
│                                                              │
│              Prompt-Driven Development                       │
│                                                              │
│              github.com/pdd-dev/pdd                          │
│                                                              │
│              $ uv tool install pdd-cli                       │
│                                                              │
│                                                              │
│                                                              │
│                                                              │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

### Animation Sequence

1. **Frame 0-45 (0-1.5s):** Fade to black
   - Previous scene opacity: 1.0 -> 0.0
   - Background color transitions: #1a1a2e -> #000000
   - All previous elements gone

2. **Frame 45-90 (1.5-3s):** Title appears
   - "Prompt-Driven Development" fades in
   - Slow, dignified fade (not instant)
   - Centered, clean

3. **Frame 90-120 (3-4s):** URL and install appear
   - URL fades in at 50% opacity
   - Install command fades in at 30% opacity
   - Sequential, each ~10 frames after the previous

4. **Frame 120-150 (4-5s):** Final hold
   - All text steady on black
   - No animation -- stillness
   - The video is complete

### Code Structure (Remotion)

```typescript
const FadeToBlack: React.FC = () => {
  const frame = useCurrentFrame();

  // Background transition to pure black
  const bgDarkness = interpolate(
    frame,
    [0, 45],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Previous scene fade-out (handled by Sequence in parent)

  // Title opacity
  const titleOpacity = interpolate(
    frame,
    [45, 80],
    [0, 0.9],
    { extrapolateRight: 'clamp' }
  );

  // URL opacity
  const urlOpacity = interpolate(
    frame,
    [85, 110],
    [0, 0.5],
    { extrapolateRight: 'clamp' }
  );

  // Install command opacity (most subtle)
  const installOpacity = interpolate(
    frame,
    [100, 125],
    [0, 0.3],
    { extrapolateRight: 'clamp' }
  );

  // Compute background color
  const r = Math.round(interpolate(bgDarkness, [0, 1], [26, 0]));
  const g = Math.round(interpolate(bgDarkness, [0, 1], [26, 0]));
  const b = Math.round(interpolate(bgDarkness, [0, 1], [46, 0]));

  return (
    <AbsoluteFill style={{
      backgroundColor: `rgb(${r}, ${g}, ${b})`,
    }}>
      {/* Title */}
      <div style={{
        position: 'absolute',
        top: '38%',
        left: 0,
        right: 0,
        textAlign: 'center',
        opacity: titleOpacity,
      }}>
        <div style={{
          fontSize: 48,
          fontWeight: 600,
          color: 'rgba(255, 255, 255, 0.9)',
          letterSpacing: 2,
          fontFamily: 'Inter, Helvetica Neue, sans-serif',
        }}>
          Prompt-Driven Development
        </div>
      </div>

      {/* URL */}
      <div style={{
        position: 'absolute',
        top: '50%',
        left: 0,
        right: 0,
        textAlign: 'center',
        opacity: urlOpacity,
      }}>
        <div style={{
          fontSize: 18,
          fontFamily: 'JetBrains Mono, monospace',
          color: 'rgba(255, 255, 255, 0.5)',
        }}>
          github.com/pdd-dev/pdd
        </div>
      </div>

      {/* Install command (subtle) */}
      <div style={{
        position: 'absolute',
        top: '56%',
        left: 0,
        right: 0,
        textAlign: 'center',
        opacity: installOpacity,
      }}>
        <div style={{
          fontSize: 16,
          fontFamily: 'JetBrains Mono, monospace',
          color: 'rgba(255, 255, 255, 0.3)',
        }}>
          <span style={{ color: 'rgba(255, 255, 255, 0.2)' }}>$ </span>
          uv tool install pdd-cli
        </div>
      </div>
    </AbsoluteFill>
  );
};
```

### Easing

- Fade to black: `easeInQuad` (gentle darkening that accelerates)
- Title fade-in: `easeOutCubic` (emerges from black)
- URL fade-in: `easeOutCubic`
- Install fade-in: `easeOutCubic`

## Narration Sync

There is no narration in this section. The previous section's narration ("The mold is what matters.") still echoes as the screen fades to black. Silence carries the title card.

## Audio Notes

- Music resolves to silence during the fade to black
- No sound effects on the title card
- If background music has been playing, it ends with a final sustained note that decays during the fade
- Pure silence by the time the install command appears
- The ending should feel like a breath being released

## Visual Style Notes

- RESTRAINT is the guiding principle
- Pure black background -- no texture, no gradient, no particles
- The title should feel authoritative but not corporate
- The URL is information, not a call-to-action
- The install command at 30% opacity is there for developers who are already interested -- it should be discoverable, not prominent
- No logos, no branding beyond the name
- This is how 3Blue1Brown ends videos: clean, quiet, respectful of the viewer
- The transition from the emotional climax (6.6) to this stillness is itself a statement

## Typography Notes

- Title: Sans-serif, clean weight, generous letter-spacing
- URL: Monospace, links to the project without being a billboard
- Install command: Monospace, preceded by `$` to signal "this is a terminal command"
- All text centered, vertically spaced with breathing room
- No underlines, no colors beyond white at varying opacities

## PDD Commands Shown

| Command | Context |
|---------|---------|
| `uv tool install pdd-cli` | Final title card, 30% opacity, for interested developers |

## Transition

This is the final section of the video. No transition -- hold on black until the video ends.
