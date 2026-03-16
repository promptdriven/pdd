[split:]

# Section 6.6: Value Migration — Code to Specification Split

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 23:00 - 23:08

## Visual Description
A split-screen showing the fundamental shift in where value resides. LEFT side: "Before" — a traditional code file (`auth_module.py`) with syntax-highlighted lines. The file is long, scrolling, fragile-looking. A faint deprecation warning overlays it. RIGHT side: "After" — a concise prompt specification (`auth_module.md`) alongside a test suite. The prompt is short (20 lines vs. 200), clean, and readable. A small arrow labeled "value" migrates from left to right across the divider — the value that was locked in implementation code now lives in the specification. This is the core thesis made visual.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F1923` (dark blue-black)
- Vertical divider: 2px, `#FFFFFF` at 15% opacity, centered at X=960

### Chart/Visual Elements
- **Left Panel — "Code as Source of Truth" (X: 0-958)**
  - Header: "Before: Code as Source" — `#D9944A`, 20px, Inter SemiBold, at (80, 60)
  - Code file mockup: 700×600px rectangle at (480, 420), `#111827` background, border-radius 8px
    - File tab: "auth_module.py" — JetBrains Mono, 13px, `#94A3B8`, with Python icon
    - ~35 lines of simulated syntax-highlighted code (line numbers in `#4A5568`, keywords in `#C084FC`, strings in `#34D399`, comments in `#64748B`)
    - Lines overflow the visible area — scroll indicator at right edge
  - Deprecation overlay: Semi-transparent red banner at bottom — "⚠ 3 deprecated APIs" — `#EF4444` at 0.2 bg, text `#EF4444` at 0.6, 14px
  - Line count badge: "~200 lines" — `#94A3B8`, 14px, bottom-left of code block

- **Right Panel — "Prompt as Source of Truth" (X: 962-1920)**
  - Header: "After: Prompt as Source" — `#4A90D9`, 20px, Inter SemiBold, at (1040, 60)
  - Prompt file mockup: 340×300px rectangle at (1200, 300), `#111827` background, border-radius 8px
    - File tab: "auth_module.md" — JetBrains Mono, 13px, `#94A3B8`, with document icon
    - ~15 lines of clean natural language spec (short, readable)
    - Golden left border accent: 3px, `#FBBF24` at 0.3 opacity
  - Test file mockup: 340×240px rectangle at (1200, 640), `#111827` background
    - File tab: "test_auth.py" — JetBrains Mono, 13px, `#94A3B8`
    - ~10 lines of test assertions
    - Green left border accent: 3px, `#5AAA6E` at 0.3 opacity
  - Line count badge: "~20 lines + tests" — `#94A3B8`, 14px, bottom-right
  - Spaciousness: Visible empty space between the two files — clean and intentional

- **Value Arrow (center):**
  - Horizontal arrow crossing the divider from left to right at Y=440
  - Arrow body: 120px long, `#FBBF24` at 0.5 opacity, 2px stroke
  - Arrowhead: `#FBBF24` at 0.5 opacity
  - Label: "value" — `#FBBF24` at 0.6 opacity, 14px, Inter italic, above arrow

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Divider draws top-to-bottom. Panel headers fade in simultaneously
2. **Frame 20-80 (0.67-2.67s):** Left panel: Code file fades in. Lines appear rapidly (simulated code scroll). Deprecation warning pulses in. Creates visual density/weight
3. **Frame 80-140 (2.67-4.67s):** Right panel: Prompt file slides in from right with 30px drift. Test file follows (20-frame stagger). Both files feel lighter — fewer lines, more whitespace
4. **Frame 140-180 (4.67-6.0s):** Value arrow draws from left to right across the divider. The label "value" fades in above it. Left panel dims slightly (opacity 1.0→0.7). Right panel brightens slightly (subtle glow on golden border)
5. **Frame 180-210 (6.0-7.0s):** Line count badges fade in on both sides. "~200 lines" vs "~20 lines + tests" makes the contrast explicit
6. **Frame 210-240 (7.0-8.0s):** Hold. Prompt file golden border breathes (0.3→0.4→0.3 opacity)

### Typography
- Panel Headers: Inter, 20px, semi-bold (600), respective panel colors
- File Tabs: JetBrains Mono, 13px, regular, `#94A3B8`
- Code Lines: JetBrains Mono, 12px, regular, syntax colors
- Line Count Badges: Inter, 14px, regular (400), `#94A3B8`
- Value Arrow Label: Inter, 14px, italic, `#FBBF24` at 0.6 opacity
- Deprecation Warning: Inter, 14px, regular, `#EF4444` at 0.6 opacity

### Easing
- Divider draw: `easeInOut(cubic)`
- Code file fade: `easeOut(quad)`
- Prompt/test file slide: `easeOut(cubic)`
- Value arrow draw: `easeInOut(cubic)`
- Panel dim/brighten: `easeInOut(quad)`
- Badge fade: `easeOut(quad)`

## Narration Sync
> "Just a gradual migration of where value lives, from code to specification."

Segment: `where_to_start_002` (19.50s – 24.86s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0F1923' }}>
    {/* Divider */}
    <Sequence from={0} durationInFrames={20}>
      <DrawOnDivider x={960} />
      <PanelHeader text="Before: Code as Source" x={80} y={60} color="#D9944A" />
      <PanelHeader text="After: Prompt as Source" x={1040} y={60} color="#4A90D9" />
    </Sequence>

    {/* Left Panel — Code File */}
    <Sequence from={20} durationInFrames={60}>
      <CodeFileMockup
        filename="auth_module.py"
        lineCount={35}
        x={480}
        y={420}
        width={700}
        height={600}
      />
      <DeprecationBanner text="⚠ 3 deprecated APIs" />
    </Sequence>

    {/* Right Panel — Prompt + Tests */}
    <Sequence from={80} durationInFrames={60}>
      <PromptFileMockup
        filename="auth_module.md"
        lineCount={15}
        x={1200}
        y={300}
        accentColor="#FBBF24"
      />
      <Sequence from={20}>
        <TestFileMockup
          filename="test_auth.py"
          lineCount={10}
          x={1200}
          y={640}
          accentColor="#5AAA6E"
        />
      </Sequence>
    </Sequence>

    {/* Value Arrow */}
    <Sequence from={140} durationInFrames={40}>
      <ValueArrow
        y={440}
        color="#FBBF24"
        label="value"
        length={120}
      />
    </Sequence>

    {/* Line Count Badges */}
    <Sequence from={180} durationInFrames={30}>
      <Badge text="~200 lines" side="left" />
      <Badge text="~20 lines + tests" side="right" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F1923",
  "leftPanel": {
    "header": "Before: Code as Source",
    "headerColor": "#D9944A",
    "file": {
      "name": "auth_module.py",
      "lineCount": 200,
      "displayLines": 35,
      "deprecatedAPIs": 3
    }
  },
  "rightPanel": {
    "header": "After: Prompt as Source",
    "headerColor": "#4A90D9",
    "promptFile": {
      "name": "auth_module.md",
      "lineCount": 20,
      "accentColor": "#FBBF24"
    },
    "testFile": {
      "name": "test_auth.py",
      "lineCount": 10,
      "accentColor": "#5AAA6E"
    }
  },
  "valueArrow": {
    "color": "#FBBF24",
    "label": "value",
    "y": 440,
    "length": 120
  }
}
```

---
