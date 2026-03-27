[Remotion]

# Section 6.2: Legacy Codebase Reveal

**Tool:** Remotion
**Duration:** ~9s (270 frames @ 30fps)
**Timestamp:** 0:00 - 0:09

## Visual Description

A large, intimidating codebase fills the screen. Dense code scrolls slowly upward — hundreds of lines of real-looking legacy code. Scattered throughout are the telltale comments of legacy software: `// don't touch`, `// here be dragons`, `// TODO: fix this (2019)`, `// nobody knows why this works`. The comments are highlighted in a warning amber while the surrounding code stays a muted slate.

The overall feeling should be dread — this is the codebase every developer inherits. The code is dense, tangled, and clearly accreted over years. File tabs at the top show names like `auth_handler.py`, `payment_processor.py`, `legacy_utils.py`, `config_v2_final_FINAL.py`.

The visual slowly zooms out to show the full scope — this isn't one file, it's an entire project. The scale is overwhelming.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid — replaced by code editor chrome

### Chart/Visual Elements

#### Code Editor Chrome
- Top bar: `#1E293B`, 40px height, with file tabs
- File tabs: `auth_handler.py` (active, `#0A0F1A`), `payment_processor.py`, `legacy_utils.py`, `config_v2_final_FINAL.py` — Inter 12px, `#94A3B8`
- Line numbers: `#334155`, left gutter 50px wide
- Code text: JetBrains Mono, 13px, `#94A3B8` at 0.7

#### Code Content (representative lines)
- Keywords: `#C792EA` (purple) — `def`, `class`, `if`, `return`, `import`
- Strings: `#C3E88D` (green)
- Functions/methods: `#82AAFF` (blue)
- Regular code: `#A6ACCD` (slate)

#### Warning Comments (highlighted)
- `// don't touch` — `#D9944A` at 0.9, with subtle amber glow background (`#D9944A` at 0.06)
- `// here be dragons` — same styling
- `// TODO: fix this (2019)` — same styling
- `// nobody knows why this works` — same styling
- Comments scattered at lines ~15, ~42, ~78, ~105

#### Zoom Indicators
- As zoom-out begins: file boundary lines appear as thin `#334155` at 0.3 dividers
- Multiple files become visible in minimap-style density

### Animation Sequence
1. **Frame 0-30 (0-1s):** Code editor fades in. Code already visible, scrolling slowly upward at 0.5px/frame.
2. **Frame 30-60 (1-2s):** First warning comment scrolls into view: `// don't touch`. Amber highlight pulses once.
3. **Frame 60-120 (2-4s):** More comments appear as code scrolls. `// here be dragons` slides into view. Each pulses on appearance.
4. **Frame 120-180 (4-6s):** Camera begins slow zoom-out. Individual lines start becoming smaller. More files become visible.
5. **Frame 180-240 (6-8s):** Zoomed out enough to see 4-5 files side by side. Dense. Overwhelming. Warning comments glow as amber dots in the density.
6. **Frame 240-270 (8-9s):** Hold at full zoom-out. The codebase fills the screen as a dense block. Transition glow begins on one module.

### Typography
- Code: JetBrains Mono, 13px → scales down during zoom
- File tabs: Inter, 12px, semi-bold (600), `#94A3B8`
- Warning comments: JetBrains Mono, 13px, `#D9944A`

### Easing
- Scroll: linear, constant 0.5px/frame
- Comment highlight pulse: `easeInOut(sine)` over 20 frames
- Zoom-out: `easeInOut(cubic)` over 120 frames
- Amber dot glow: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "PDD can create prompts from existing code."

Segment: `where_to_start_001` (first portion, 0.00s - 9.00s approx)

- **0.00s** (seg 001): Code editor fades in, scrolling begins
- **1.00s**: First warning comment visible
- **4.00s**: Zoom-out begins — "PDD can create prompts from existing code"
- **9.00s**: Fully zoomed out, one module begins to glow

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={270}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Code editor chrome */}
    <EditorChrome
      tabs={["auth_handler.py", "payment_processor.py", "legacy_utils.py", "config_v2_final_FINAL.py"]}
      activeTab={0}
    />

    {/* Scrolling code with warning comments */}
    <Sequence from={0}>
      <ScrollingCode
        scrollSpeed={0.5}
        syntax="python"
        warningComments={[
          { line: 15, text: "# don't touch" },
          { line: 42, text: "# here be dragons" },
          { line: 78, text: "# TODO: fix this (2019)" },
          { line: 105, text: "# nobody knows why this works" },
        ]}
        warningColor="#D9944A"
        warningGlow={{ color: "#D9944A", opacity: 0.06 }}
      />
    </Sequence>

    {/* Zoom-out camera */}
    <Sequence from={120}>
      <ZoomCamera
        fromScale={1.0} toScale={0.25}
        duration={120} easing="easeInOutCubic"
        center={[960, 540]}
      />
    </Sequence>

    {/* Module highlight glow (prepares for next spec) */}
    <Sequence from={240}>
      <FadeIn duration={30}>
        <ModuleGlow
          target="auth_handler"
          color="#5AAA6E" opacity={0.15}
          radius={60}
        />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_editor_animation",
  "editorId": "legacy_codebase_reveal",
  "files": [
    "auth_handler.py",
    "payment_processor.py",
    "legacy_utils.py",
    "config_v2_final_FINAL.py"
  ],
  "warningComments": [
    { "line": 15, "text": "# don't touch" },
    { "line": 42, "text": "# here be dragons" },
    { "line": 78, "text": "# TODO: fix this (2019)" },
    { "line": 105, "text": "# nobody knows why this works" }
  ],
  "narrationSegments": ["where_to_start_001"]
}
```

---
