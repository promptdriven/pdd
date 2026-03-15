[split:]

# Section 0.2: Split Screen — Craft Parallel

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 0:03 - 0:15

## Visual Description
A vertical split screen divides the frame precisely in half. **Left side:** A stylized developer workspace — a code editor (dark theme) with a Cursor-like interface. Animated lines of code appear and a highlighted diff-style patch lands cleanly on a function. The edit is slick, satisfying. **Right side:** A stylized illustration of a 1950s grandmother darning a wool sock by warm lamplight. Her needle pulls thread through fabric in a rhythmic, careful motion. Both sides complete their repair task simultaneously, emphasizing the parallel: modern AI-assisted coding is just a faster version of the same careful mending.

The visual style is geometric and clean — not photorealistic. The developer side uses flat UI shapes with code-editor colors. The grandmother side uses warm, muted tones with simple geometric shapes (circles for yarn, rectangles for fabric).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Left `#1A1B26` (editor dark), Right `#2D1F14` (warm sepia dark)
- Grid lines: None
- Vertical divider: 2px, `#FFFFFF` at 30% opacity, X=960

### Chart/Visual Elements
- **Left Panel (Code Editor):**
  - Editor chrome: tab bar at top, line numbers column `#4A5568`, gutter
  - Code lines: 15-20 lines of monospace text, syntax-colored (strings `#A3BE8C`, keywords `#81A1C1`, functions `#88C0D0`)
  - Diff highlight: green `+` lines `rgba(80, 200, 120, 0.15)` background glow on lines 8-12
  - Cursor: blinking bar at line 10
  - Subtle Cursor-like AI suggestion ghost text in `#4A5568` opacity 0.4

- **Right Panel (Grandmother):**
  - Lamplight: warm radial gradient from `#D4A574` center to `#2D1F14` edges, centered at top-right
  - Sock shape: rounded rectangle, `#8B7355` with `#5C4A32` darning grid visible
  - Needle: thin white line `#E8D5C0`, 40px long, animated along a stitching path
  - Thread trail: `#C49A6C` line following needle path, accumulating

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split screen slides in — left panel from left, right panel from right, meeting at center divider
2. **Frame 15-30 (0.5-1.0s):** Left: code editor content fades in. Right: lamplight glow intensifies from dim to warm
3. **Frame 30-120 (1.0-4.0s):** Both sides animate simultaneously:
   - Left: AI ghost text appears on lines 8-12, then "accepts" — code solidifies with green diff highlight
   - Right: Needle makes 4 stitching passes across the sock hole (arc paths), thread trail follows
4. **Frame 120-150 (4.0-5.0s):** Narration: "...you're getting really good at this."
   - Left: green checkmark fades in next to the diff
   - Right: needle rests, last stitch completes, thread snips (small white flash)
5. **Frame 150-360 (5.0-12.0s):** Hold on completed state. Both sides show their finished, satisfying repair work. Subtle idle animations (cursor blink left, gentle lamplight flicker right)

### Typography
- Left panel line numbers: JetBrains Mono, 14px, `#4A5568`
- Left panel code: JetBrains Mono, 16px, various syntax colors
- No visible text labels on right panel

### Easing
- Panel slide-in: `easeOut(cubic)`
- Code fade-in: `easeOut(quad)`
- Needle arc path: `easeInOut(sin)` per stitch pass
- Lamplight glow: `easeOut(quad)`
- Checkmark fade: `easeOut(quad)`

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot... you're getting really good at this."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  {/* Left Panel — Code Editor */}
  <Sequence from={0}>
    <SlideIn direction="left" durationInFrames={15}>
      <CodeEditorPanel background="#1A1B26">
        <CodeLines lines={codeContent} syntaxTheme="nord" />
        <Sequence from={30}>
          <AIDiffAccept lines={[8, 9, 10, 11, 12]} highlightColor="rgba(80, 200, 120, 0.15)" />
        </Sequence>
        <Sequence from={120}>
          <FadeIn><Checkmark color="#50C878" /></FadeIn>
        </Sequence>
      </CodeEditorPanel>
    </SlideIn>
  </Sequence>

  {/* Vertical Divider */}
  <VerticalDivider x={960} color="#FFFFFF" opacity={0.3} />

  {/* Right Panel — Grandmother Darning */}
  <Sequence from={0}>
    <SlideIn direction="right" durationInFrames={15}>
      <DarningPanel background="#2D1F14">
        <LampGlow center={[1680, 120]} color="#D4A574" />
        <SockShape position={[1440, 540]} />
        <Sequence from={30}>
          <StitchingNeedle
            passes={4}
            framesPerPass={22}
            threadColor="#C49A6C"
          />
        </Sequence>
      </DarningPanel>
    </SlideIn>
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "leftPanel": {
    "background": "#1A1B26",
    "editorTheme": "nord",
    "diffLines": [8, 9, 10, 11, 12],
    "diffHighlight": "rgba(80, 200, 120, 0.15)"
  },
  "rightPanel": {
    "background": "#2D1F14",
    "lampColor": "#D4A574",
    "sockColor": "#8B7355",
    "threadColor": "#C49A6C",
    "stitchPasses": 4
  },
  "divider": {
    "x": 960,
    "color": "#FFFFFF",
    "opacity": 0.3,
    "width": 2
  }
}
```

---
