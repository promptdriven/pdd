[Remotion]

# Section 0.5: Code Cursor Blink — The Patching Question

**Tool:** Remotion
**Duration:** ~7s (210 frames @ 30fps)
**Timestamp:** 0:19 - 0:26

## Visual Description

Return to the code side. A dark-themed code editor fills the screen, showing a complex function riddled with patches. The function is `process_order()` — roughly 40 lines visible, dense with inline comments like `# HACK: workaround for #2847`, `# TODO: refactor this`, `# PATCH: edge case from v2.3`. Diff markers (`+`, `|`) line the gutter. The cursor blinks at the top of the function — a steady, patient pulse. The viewer sits with the accumulated weight of all that patching. Then the narration asks the pivotal question: "why are we still patching?"

The code is synthetic but realistic: a Python function with layered fixes, bandaids, and workarounds. It should feel exhausting to look at — the visual equivalent of tech debt.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#1E1E2E` (VS Code dark theme)
- Gutter: `#2D2D3D`, 60px wide
- Line highlight: Current line at `#2A2A3A`

### Chart/Visual Elements

#### Code Editor Chrome
- Title bar: `#181825` with filename `process_order.py` in `#CDD6F4`
- Tab: Active tab with dot indicator (modified)
- Line numbers: `#6C7086` in JetBrains Mono 14px
- Gutter markers: Orange `|` for modified lines, green `+` for added

#### Code Content
- Function signature: `def process_order(order, user, config):` in `#89B4FA` (blue)
- Comments: `#6C7086` (muted gray) — but HACK/TODO/PATCH keywords in `#F38BA8` (red)
- Strings: `#A6E3A1` (green)
- Keywords: `#CBA6F7` (purple)
- Regular code: `#CDD6F4` (light)
- Approximately 35-40 visible lines with at least 6 patch comments scattered throughout

#### Cursor
- Position: Line 1, after function signature
- Color: `#CDD6F4`
- Width: 2px, height: 20px
- Blink: 530ms on, 530ms off (standard VS Code timing)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Editor fades in from black. Code is immediately visible, dense and patched.
2. **Frame 15-90 (0.5-3s):** Camera slow-scrolls down through the function, revealing layer upon layer of patches and workarounds. Cursor remains at top, blinking.
3. **Frame 90-150 (3-5s):** Scroll stops. The full function is visible. "Code just got that cheap!" — the cursor blinks patiently. HACK/TODO comments subtly pulse with a faint red glow.
4. **Frame 150-210 (5-7s):** "why are we still patching?" — The cursor blinks hold. Beat. The entire code block begins a very subtle fade, preparing for the next spec's dramatic delete.

### Typography
- Code: JetBrains Mono, 14px, various syntax colors
- Title bar: Inter, 13px, `#CDD6F4`
- No overlay text — narration carries the question

### Easing
- Fade-in: `easeOut(quad)` over 15 frames
- Code scroll: `easeInOut(cubic)` over 75 frames
- Comment pulse: `easeInOut(sine)` on 60-frame cycle, opacity 0.7→1.0
- Code pre-fade: `easeIn(quad)` over 60 frames, opacity 1.0→0.85

## Narration Sync
> "Code just got that cheap!"
> "why are we still patching?"

Segments: `cold_open_005`, `cold_open_006`

- **19.50s** (seg 005): Editor fades in, patched code visible
- **22.70s** (seg 005 ends / seg 006 begins): "Code just got that cheap!" — scroll reveals full function
- **26.18s** (seg 006 ends): "why are we still patching?" — cursor blinks, beat

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={210}>
  {/* Editor background */}
  <CodeEditorChrome
    filename="process_order.py"
    theme="catppuccin-mocha"
  />

  {/* Code content with scroll */}
  <Sequence from={15} durationInFrames={195}>
    <CodeBlock
      code={PROCESS_ORDER_CODE}
      language="python"
      scrollStart={0}
      scrollEnd={400}
      scrollDuration={75}
      scrollDelay={0}
      easing="easeInOutCubic"
    />
  </Sequence>

  {/* Blinking cursor */}
  <Sequence from={0} durationInFrames={210}>
    <BlinkingCursor
      line={1}
      blinkMs={530}
      color="#CDD6F4"
    />
  </Sequence>

  {/* HACK/TODO comment pulse */}
  <Sequence from={90} durationInFrames={120}>
    <CommentPulse
      keywords={["HACK", "TODO", "PATCH"]}
      color="#F38BA8"
      cycleFrames={60}
      minOpacity={0.7}
    />
  </Sequence>

  {/* Pre-fade for transition */}
  <Sequence from={150} durationInFrames={60}>
    <FadeOpacity from={1.0} to={0.85} easing="easeInQuad" />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "remotion_animation",
  "componentId": "code_cursor_blink",
  "durationFrames": 210,
  "fps": 30,
  "narrationSegments": ["cold_open_005", "cold_open_006"],
  "codeFile": "process_order.py",
  "patchComments": 6,
  "visibleLines": 40
}
```

---
