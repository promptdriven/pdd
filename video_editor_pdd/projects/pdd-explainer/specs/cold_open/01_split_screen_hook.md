[split:]

# Section 0.1: Split Screen Hook — Developer Meets Grandmother

**Tool:** Split
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:00 - 0:08

## Visual Description

The video opens on a clean vertical split screen. LEFT side: a developer's screen showing a Cursor-style IDE interface — dark theme, a code file open, an AI-assisted inline edit completing in real time. The edit highlights in green as it lands. RIGHT side: a 1950s domestic scene rendered as a stylized illustration — a grandmother seated by lamplight, needle and thread in hand, carefully darning a wool sock stretched over a wooden darning egg.

Both sides animate simultaneously. The code edit lands cleanly on the left; the final stitch pulls tight on the right. A thin vertical divider (1px, white at 20% opacity) separates the two halves. The overall palette is dark and cinematic — the left side uses Cursor's dark UI tones, the right uses warm sepia-tinged lamplight.

At the midpoint, both sides complete their task in sync — the edit confirms with a green flash, the stitch finishes with a taut thread. The parallel is unmistakable: both are careful, skilled repair work.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0A0F1A (deep charcoal)
- Vertical divider: 1px solid rgba(255,255,255,0.2) at x=960

### Chart/Visual Elements

**Left Panel (Developer Side) — x: 0-959**

- IDE mockup: dark background #1E1E2E, sidebar #16161E
- Code file: monospace text in muted syntax colors (strings: #A9DC76, keywords: #78DCE8, functions: #FFD866)
- AI edit highlight: green glow #5AAA6E at 30% opacity, animating in from cursor position
- Cursor blink: white #FFFFFF, 500ms interval
- File tab: "auth_handler.py" in #9CA3AF, 12px

**Right Panel (Grandmother Side) — x: 961-1920**

- Warm background gradient: #2A1F14 → #1A1308 (top to bottom)
- Lamplight glow: radial gradient from #D4A043 at 40% opacity, centered at (1600, 200)
- Grandmother figure: stylized silhouette with warm fill #8B6914
- Sock on darning egg: wool texture in #C4956A, needle glint #FFFFFF at 60% opacity
- Thread line: animated bezier curve, #D4A043, 2px stroke

**Vertical Divider**

- Position: x=960, full height
- Color: rgba(255,255,255,0.2)
- Width: 1px

### Animation Sequence

1. **Frame 0-20 (0-0.67s):** Both panels fade in from black simultaneously. Opacity 0 → 1, `easeOut(cubic)`. Divider draws top-to-bottom.
2. **Frame 20-90 (0.67-3.0s):** LEFT: AI edit types out 3 lines of code character-by-character, green highlight sweeps left-to-right behind the text. RIGHT: Grandmother's hand makes 4 stitching motions, thread curves animate along bezier path.
3. **Frame 90-130 (3.0-4.33s):** LEFT: Edit completes, green highlight pulses once then settles to 15% opacity. A faint `✓` appears at line end. RIGHT: Final stitch pulls tight, needle rests. Grandmother's hand settles. Thread taut.
4. **Frame 130-180 (4.33-6.0s):** Both sides hold. Subtle ambient animations only — cursor blinking left, lamplight flickering right. The parallel sits with the viewer.
5. **Frame 180-240 (6.0-8.0s):** Hold continues through second narration line. Both tasks are done; the craftsmanship is evident on both sides.

### Typography

- File tab label: `JetBrains Mono`, 12px, #9CA3AF
- No other text elements (narration carries the content)

### Easing

- Panel fade-in: `easeOut(cubic)`
- Divider draw: `easeInOut(cubic)`
- Code typing: `linear` (character-by-character)
- Green highlight sweep: `easeInOut(cubic)`
- Stitch motion: `easeInOut(sin)`
- Lamplight flicker: `easeInOut(sin)` with randomized amplitude

## Narration Sync

> "If you use Cursor, or Claude Code, or Copilot..."
Segment: `cold_open_001`
Timing: 0:00 - 0:04

> "...you're getting really good at this."
Segment: `cold_open_002`
Timing: 0:04 - 0:08

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Vertical Divider */}
    <Sequence from={0} durationInFrames={20}>
      <DividerDraw x={960} color="rgba(255,255,255,0.2)" />
    </Sequence>

    {/* Left Panel — Developer */}
    <AbsoluteFill style={{ clipPath: 'inset(0 50% 0 0)' }}>
      <IDEMockup theme="dark" fileName="auth_handler.py" />
      <Sequence from={20} durationInFrames={70}>
        <AIEditAnimation lines={3} highlightColor="#5AAA6E" />
      </Sequence>
      <Sequence from={90} durationInFrames={150}>
        <BlinkingCursor line={4} />
      </Sequence>
    </AbsoluteFill>

    {/* Right Panel — Grandmother */}
    <AbsoluteFill style={{ clipPath: 'inset(0 0 0 50%)' }}>
      <LamplightScene gradient={['#2A1F14', '#1A1308']} />
      <Sequence from={20} durationInFrames={70}>
        <DarningAnimation stitches={4} threadColor="#D4A043" />
      </Sequence>
    </AbsoluteFill>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON

```json
{
  "layout": {
    "splitX": 960,
    "divider": { "width": 1, "color": "rgba(255,255,255,0.2)" }
  },
  "leftPanel": {
    "ide": {
      "background": "#1E1E2E",
      "sidebar": "#16161E",
      "fileName": "auth_handler.py",
      "syntaxColors": {
        "strings": "#A9DC76",
        "keywords": "#78DCE8",
        "functions": "#FFD866"
      }
    },
    "aiEdit": {
      "highlightColor": "#5AAA6E",
      "highlightOpacity": 0.3,
      "settledOpacity": 0.15,
      "lineCount": 3
    }
  },
  "rightPanel": {
    "background": ["#2A1F14", "#1A1308"],
    "lamplight": {
      "color": "#D4A043",
      "opacity": 0.4,
      "center": [1600, 200]
    },
    "thread": {
      "color": "#D4A043",
      "strokeWidth": 2,
      "stitchCount": 4
    }
  },
  "narrationSegments": ["cold_open_001", "cold_open_002"],
  "narrationTimingSeconds": { "start": 0.0, "end": 8.0 }
}
```

---
