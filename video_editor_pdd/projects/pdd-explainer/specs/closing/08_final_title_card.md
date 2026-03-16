[title:]

# Section 7.8: Final Title Card — Prompt-Driven Development

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 25:09 - 25:17

## Visual Description
Fade to black. Then, from the darkness, the title emerges: "Prompt-Driven Development" in clean, confident typography — the kind of title card that closes a documentary. Below the title, a thin horizontal rule. Below that, two lines of terminal-style text providing the practical next step: `uv tool install pdd-cli` and `pdd update your_module.py`. This is the call to action — not a sales pitch, just a quiet invitation. The URL appears at the very bottom. Everything is centered, balanced, and unhurried. The viewer leaves with the name, the concept, and the command to try it.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#060A12` (near-black), settling from the previous shot's fade
- Grid lines: None

### Chart/Visual Elements
- **Title:** "Prompt-Driven Development" — `#FFFFFF` at 0.9 opacity, 48px Inter semi-bold (600), centered at (960, 380), letter-spacing 2px
- **Thin Horizontal Rule:** 120px wide, 1px, `rgba(255,255,255,0.2)`, centered at (960, 440)
- **Install Command Block:**
  - Container: Rounded rectangle, `#0D1117` fill, border `rgba(255,255,255,0.06)`, border-radius 8px, 600x100px, centered at (960, 540)
  - Line 1: `$ uv tool install pdd-cli` — `#C9D1D9`, 16px JetBrains Mono, left-aligned with 24px padding. `$` in `#6E7681`, `uv tool install` in `#C9D1D9`, `pdd-cli` in `#4A90D9`
  - Line 2: `$ pdd update your_module.py` — same styling. `pdd update` in `#C9D1D9`, `your_module.py` in `#5AAA6E`
- **URL:** "pdd.dev" — `#4A90D9` at 0.6 opacity, 18px Inter regular, centered at (960, 700)
- **Subtle Triangle Ghost:** The PDD triangle from previous shots, extremely faint — edges at `rgba(255,255,255,0.01)`, nodes as 6px dots at 0.02 opacity in their respective colors. Positioned behind the title as a watermark, scaled to 40% of original size, centered at (960, 380). Almost invisible but rewards close attention
- **Copyright/Attribution (optional):** `© 2025` — `rgba(255,255,255,0.15)`, 12px Inter, centered at (960, 1020)

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Background settles to `#060A12`. Ghost triangle watermark fades in at near-invisible opacity. A moment of darkness before the title
2. **Frame 30-70 (1.0-2.33s):** Title "Prompt-Driven Development" fades in — opacity 0→0.9 with 6px upward drift. Each word can have a very slight stagger (3 frames between "Prompt-Driven" and "Development") for elegance
3. **Frame 70-90 (2.33-3.0s):** Horizontal rule draws from center outward (0→120px), `rgba(255,255,255,0.2)`
4. **Frame 90-140 (3.0-4.67s):** Command block slides up gently (Y+10→Y) and fades in. Line 1 types out character by character (1.5 frames/char): `$ uv tool install pdd-cli`. Color syntax highlighting applies as each word completes
5. **Frame 140-180 (4.67-6.0s):** Line 2 types out: `$ pdd update your_module.py`. A blinking cursor appears at the end (blinks every 30 frames, `#C9D1D9` at 0.5 opacity)
6. **Frame 180-210 (6.0-7.0s):** URL "pdd.dev" fades in at bottom, subtle and unassuming
7. **Frame 210-240 (7.0-8.0s):** Hold at final state. Cursor continues blinking. All elements rest. The frame is complete

### Typography
- Title: Inter, 48px, semi-bold (600), `#FFFFFF` at 0.9 opacity, letter-spacing 2px
- Terminal commands: JetBrains Mono, 16px, regular (400), `#C9D1D9`
- Terminal prompt: JetBrains Mono, 16px, regular (400), `#6E7681`
- Highlighted package name: JetBrains Mono, 16px, regular (400), `#4A90D9`
- Highlighted filename: JetBrains Mono, 16px, regular (400), `#5AAA6E`
- URL: Inter, 18px, regular (400), `#4A90D9` at 0.6 opacity
- Copyright: Inter, 12px, regular (400), `rgba(255,255,255,0.15)`

### Easing
- Title fade/drift: `easeOut(quad)`
- Horizontal rule draw: `easeOut(cubic)`
- Command block slide-up: `easeOut(quad)`
- Character typing: linear (typewriter)
- URL fade: `easeOut(quad)`
- Cursor blink: step function (instant on/off)

## Narration Sync
> *(No narration — music/ambient only. This is the end card.)*

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#060A12' }}>
    {/* Ghost Triangle Watermark */}
    <Sequence from={0} durationInFrames={30}>
      <GhostTriangleWatermark
        center={[960, 380]}
        scale={0.4}
        edgeOpacity={0.01}
        nodeOpacity={0.02}
      />
    </Sequence>

    {/* Title */}
    <Sequence from={30} durationInFrames={40}>
      <FadeText
        text="Prompt-Driven Development"
        fontSize={48}
        fontWeight={600}
        color="#FFFFFF"
        opacity={0.9}
        y={380}
        driftY={-6}
        letterSpacing={2}
        align="center"
      />
    </Sequence>

    {/* Horizontal Rule */}
    <Sequence from={70} durationInFrames={20}>
      <AccentLine
        targetWidth={120}
        y={440}
        color="rgba(255,255,255,0.2)"
        strokeWidth={1}
      />
    </Sequence>

    {/* Command Block */}
    <Sequence from={90} durationInFrames={90}>
      <TerminalCard x={660} y={490} width={600} height={100}>
        <TypewriterLine
          from={0}
          prompt="$"
          segments={[
            { text: "uv tool install ", color: "#C9D1D9" },
            { text: "pdd-cli", color: "#4A90D9" },
          ]}
          charSpeed={1.5}
        />
        <TypewriterLine
          from={50}
          prompt="$"
          segments={[
            { text: "pdd update ", color: "#C9D1D9" },
            { text: "your_module.py", color: "#5AAA6E" },
          ]}
          charSpeed={1.5}
        />
        <BlinkingCursor from={90} color="#C9D1D9" blinkRate={30} />
      </TerminalCard>
    </Sequence>

    {/* URL */}
    <Sequence from={180} durationInFrames={30}>
      <FadeText
        text="pdd.dev"
        fontSize={18}
        color="#4A90D9"
        opacity={0.6}
        y={700}
        align="center"
      />
    </Sequence>

    {/* Copyright */}
    <Sequence from={180} durationInFrames={30}>
      <FadeText
        text="© 2025"
        fontSize={12}
        color="rgba(255,255,255,0.15)"
        y={1020}
        align="center"
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#060A12",
  "title": {
    "text": "Prompt-Driven Development",
    "fontSize": 48,
    "fontWeight": 600,
    "opacity": 0.9,
    "y": 380,
    "letterSpacing": 2
  },
  "rule": {
    "width": 120,
    "y": 440,
    "color": "rgba(255,255,255,0.2)"
  },
  "commands": [
    {
      "prompt": "$",
      "segments": [
        { "text": "uv tool install ", "color": "#C9D1D9" },
        { "text": "pdd-cli", "color": "#4A90D9" }
      ]
    },
    {
      "prompt": "$",
      "segments": [
        { "text": "pdd update ", "color": "#C9D1D9" },
        { "text": "your_module.py", "color": "#5AAA6E" }
      ]
    }
  ],
  "url": {
    "text": "pdd.dev",
    "color": "#4A90D9",
    "opacity": 0.6,
    "y": 700
  },
  "ghostTriangle": {
    "scale": 0.4,
    "edgeOpacity": 0.01,
    "nodeOpacity": 0.02
  }
}
```

---
