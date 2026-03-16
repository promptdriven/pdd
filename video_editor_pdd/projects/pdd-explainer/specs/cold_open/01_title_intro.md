[split:]

# Section 0.1: AI Tools Hook — Split Screen Intro

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:00 - 0:05

## Visual Description

The video opens on a clean vertical split screen. LEFT side: a developer's screen showing a Cursor-style IDE interface — dark theme, a code file open, an AI-assisted inline edit completing in real time. The edit highlights in green as it lands. RIGHT side: a 1950s domestic scene rendered as a stylized illustration — a grandmother seated by lamplight, needle and thread in hand, carefully darning a wool sock stretched over a wooden darning egg.

Both sides animate simultaneously. The code edit lands cleanly on the left; the final stitch pulls tight on the right. A thin vertical divider (1px, white at 20% opacity) separates the two halves. The overall palette is dark and cinematic — the left side uses Cursor's dark UI tones, the right uses warm sepia-tinged lamplight.

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
1. **Frame 0-15 (0-0.5s):** Both panels fade in from black. Opacity 0 → 1, `easeOut(cubic)`.
2. **Frame 15-60 (0.5-2.0s):** LEFT: AI edit types out 3 lines of code, green highlight sweeps left-to-right behind the text. RIGHT: Grandmother's hand makes 4 stitching motions, thread curves animate along bezier path.
3. **Frame 60-90 (2.0-3.0s):** LEFT: Edit completes, green highlight pulses once then settles to 15% opacity. RIGHT: Final stitch pulls tight, needle rests. Grandmother's hand settles.
4. **Frame 90-150 (3.0-5.0s):** Both sides hold. Subtle ambient animations only — cursor blinking left, lamplight flickering right.

### Typography
- No text elements in this scene (narration carries the content)

### Easing
- Panel fade-in: `easeOut(cubic)`
- Code typing: `linear` (character-by-character)
- Green highlight sweep: `easeInOut(cubic)`
- Stitch motion: `easeInOut(sin)`
- Lamplight flicker: `easeInOut(sin)` with randomized amplitude

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot..."
> "...you're getting really good at this."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <SplitScreen dividerX={960} dividerColor="rgba(255,255,255,0.2)">
    <Sequence from={0} durationInFrames={150}>
      <DeveloperPanel>
        <IDEMockup theme="dark" />
        <Sequence from={15} durationInFrames={45}>
          <AIEditAnimation lines={3} highlightColor="#5AAA6E" />
        </Sequence>
      </DeveloperPanel>
    </Sequence>
    <Sequence from={0} durationInFrames={150}>
      <GrandmotherPanel>
        <LamplightScene />
        <Sequence from={15} durationInFrames={45}>
          <DarningAnimation stitches={4} threadColor="#D4A043" />
        </Sequence>
      </GrandmotherPanel>
    </Sequence>
  </SplitScreen>
</Sequence>
```

## Data Points
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
  "narrationTimingSeconds": { "start": 0.0, "end": 5.5 }
}
```

---
