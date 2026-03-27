[title:]

# Section 7.7: Final Title Card — Prompt-Driven Development

**Tool:** Title
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:17 - 0:23

## Visual Description

Fade up from black. The final title card. Clean, authoritative, minimal.

Center screen: **"Prompt-Driven Development"** in large, bold white type. Below, separated by a thin horizontal rule, two monospaced lines showing the install and first-run commands:

```
uv tool install pdd-cli
pdd update your_module.py
```

A URL sits below the commands in smaller type, subtly underlined. The entire composition breathes — generous whitespace, no clutter. This is the takeaway frame: what the viewer should Google, install, and try.

The background is true black with a very faint blueprint grid (the visual motif from the entire video) at barely perceptible opacity — a whisper of continuity.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Grid lines: 60px spacing, `#1E293B` at 0.02 opacity (barely visible)

### Chart/Visual Elements

#### Main Title
- Text: "Prompt-Driven Development"
- Position: centered at (960, 360)
- Font: Inter, 64px, Bold (700)
- Color: `#E2E8F0` (light gray-blue)
- Letter-spacing: -0.5px

#### Horizontal Rule
- Position: centered at (960, 420)
- Width: 400px
- Height: 1px
- Color: `#334155` at 0.4 opacity

#### Install Commands
- Position: centered at (960, 500)
- Font: JetBrains Mono, 20px, Regular (400)
- Line 1: `uv tool install pdd-cli` — color `#94A3B8` (slate)
- Line 2: `pdd update your_module.py` — color `#4AD9A0` (teal, emphasized)
- Line spacing: 36px
- Prompt symbol: `$` in `#64748B` at 0.6 opacity, preceding each line

#### URL
- Text: "promptdrivendevelopment.com"
- Position: centered at (960, 620)
- Font: Inter, 18px, Regular (400)
- Color: `#64748B` (muted slate)
- Underline: 1px `#64748B` at 0.3 opacity

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Background fades up from true black, faint grid appears
2. **Frame 20-50 (0.67-1.67s):** Title types in character-by-character (2 frames/char for "Prompt-Driven Development" = ~50 frames)
3. **Frame 50-60 (1.67-2s):** Horizontal rule draws from center outward, `easeInOut(cubic)`
4. **Frame 60-80 (2-2.67s):** First command line types in: `$ uv tool install pdd-cli` (2 frames/char)
5. **Frame 80-105 (2.67-3.5s):** Second command line types in: `$ pdd update your_module.py` (2 frames/char)
6. **Frame 105-120 (3.5-4s):** URL fades in below, `easeOut(quad)`
7. **Frame 120-180 (4-6s):** Hold — all elements visible, subtle pulse on teal command line (90-frame `easeInOut(sine)` cycle, opacity 0.85→1.0)

### Typography
- Title: Inter, 64px, Bold (700), `#E2E8F0`
- Commands: JetBrains Mono, 20px, Regular (400)
- Command prompt `$`: JetBrains Mono, 20px, `#64748B` at 0.6
- URL: Inter, 18px, Regular (400), `#64748B`

### Easing
- Grid fade-in: `easeOut(quad)` over 20 frames
- Title type-in: linear, 2 frames per character
- Rule draw: `easeInOut(cubic)` over 10 frames
- Command type-in: linear, 2 frames per character
- URL fade-in: `easeOut(quad)` over 15 frames
- Teal pulse: `easeInOut(sine)` on 90-frame cycle

## Narration Sync
> (No narration — visual-only title card after audio ends)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  {/* Background with faint grid */}
  <Sequence from={0} durationInFrames={180}>
    <Background color="#000000" gridOpacity={0.02} fadeInFrames={20} />
  </Sequence>
  {/* Title */}
  <Sequence from={20} durationInFrames={160}>
    <TypewriterText
      text="Prompt-Driven Development"
      font="Inter"
      size={64}
      color="#E2E8F0"
      framesPerChar={2}
    />
  </Sequence>
  {/* Horizontal rule */}
  <Sequence from={50} durationInFrames={130}>
    <HorizontalRule width={400} color="#334155" opacity={0.4} drawFrames={10} />
  </Sequence>
  {/* Install commands */}
  <Sequence from={60} durationInFrames={120}>
    <TerminalLine
      prompt="$"
      command="uv tool install pdd-cli"
      color="#94A3B8"
      framesPerChar={2}
    />
  </Sequence>
  <Sequence from={80} durationInFrames={100}>
    <TerminalLine
      prompt="$"
      command="pdd update your_module.py"
      color="#4AD9A0"
      framesPerChar={2}
      pulseOnHold={true}
    />
  </Sequence>
  {/* URL */}
  <Sequence from={105} durationInFrames={75}>
    <FadeIn durationFrames={15}>
      <URLText text="promptdrivendevelopment.com" color="#64748B" />
    </FadeIn>
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "componentId": "final_title_card",
  "durationFrames": 180,
  "fps": 30,
  "narrationSegments": [],
  "title": "Prompt-Driven Development",
  "commands": [
    "uv tool install pdd-cli",
    "pdd update your_module.py"
  ],
  "url": "promptdrivendevelopment.com"
}
```

---
