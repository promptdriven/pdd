[split:]

# Section 2.9: Prompt Replaces Review — Verify the Output

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 10:31 - 10:43

## Visual Description
A split-screen transition answers the "can you review this?" question. The overwhelming code diff from the previous segment dissolves away. In its place, a clean two-panel layout appears. LEFT panel: a compact prompt document — maybe 30 lines of readable natural language, glowing softly with a warm amber border. It's obviously reviewable. RIGHT panel: a test suite with green checkmarks stacked vertically — each test name visible and concise. A horizontal bridge label connects the two panels: "Review the spec. Verify the output." The contrast is dramatic: thousands of unreviewable lines replaced by a reviewable spec and a verifiable test suite. This is the chip industry's answer applied to software.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Vertical Divider:** 2px line at X=960, Y=120 to Y=800, `rgba(255,255,255,0.08)`
- **Left Panel — Prompt Document**
  - Position: centered at (480, 440)
  - Rounded rectangle 500px x 520px, border `#D9944A` 1.5px, fill `rgba(217,148,74,0.04)`
  - Header bar: 500px x 40px, fill `rgba(217,148,74,0.1)`, text "prompt.md" — `#D9944A`, 16px, bold
  - Content: 12 lines of visible text (lorem-style but readable), JetBrains Mono, 13px, `#CBD5E1` at 0.7
  - Soft glow: `rgba(217,148,74,0.08)` radial, radius 300px, behind the document
  - Sub-label: "30 lines · Reviewable" — `#D9944A`, 14px, at Y=760
- **Right Panel — Test Suite**
  - Position: centered at (1440, 440)
  - Rounded rectangle 500px x 520px, border `#2AA198` 1.5px, fill `rgba(42,161,152,0.04)`
  - Header bar: 500px x 40px, fill `rgba(42,161,152,0.1)`, text "tests/" — `#2AA198`, 16px, bold
  - 8 test rows, each 500px x 48px:
    - Green checkmark circle (20px), `#2AA198`
    - Test name: `test_handles_null_input`, `test_unicode_output`, etc. — JetBrains Mono, 13px, `#CBD5E1`
    - Each row separated by 1px `rgba(255,255,255,0.04)` line
  - Sub-label: "8 tests · All passing" — `#2AA198`, 14px, at Y=760
- **Bridge Label**
  - Centered at (960, 860), spanning both panels
  - Text: "Review the spec. Verify the output." — `#FFFFFF`, 22px, bold
  - Thin horizontal accent lines extending left and right from the text, `rgba(255,255,255,0.2)`, 120px each

### Animation Sequence
1. **Frame 0-30 (0-1s):** Previous diff view fades out completely. Clean dark background
2. **Frame 30-60 (1-2s):** Vertical divider draws top-to-bottom
3. **Frame 60-120 (2-4s):** Left panel: prompt document fades in — border draws, header appears, then lines of text appear one by one (typewriter, 5 frames per line). Soft glow radiates outward
4. **Frame 90-160 (3-5.33s):** Right panel: test suite fades in — border draws, header appears, then test rows slide in from right one by one (staggered 6 frames apart). Green checkmarks pop in with scale bounce
5. **Frame 160-200 (5.33-6.67s):** Sub-labels fade in below both panels
6. **Frame 200-260 (6.67-8.67s):** Bridge label types in at bottom center. Accent lines extend outward from text edges
7. **Frame 260-360 (8.67-12s):** Hold at final state. Subtle breathing glow on both panels

### Typography
- Document Header: JetBrains Mono, 16px, bold (700), `#D9944A`
- Document Content: JetBrains Mono, 13px, regular (400), `#CBD5E1` at 0.7
- Test Suite Header: JetBrains Mono, 16px, bold (700), `#2AA198`
- Test Names: JetBrains Mono, 13px, regular (400), `#CBD5E1`
- Sub-labels: Inter, 14px, medium (500), respective panel colors
- Bridge Label: Inter, 22px, bold (700), `#FFFFFF`

### Easing
- Diff fade-out: `easeIn(quad)`
- Divider draw: `easeOut(cubic)`
- Document fade/draw: `easeOut(quad)`
- Text typewriter: `linear`
- Test row slide-in: `easeOut(cubic)` per row
- Checkmark pop: `easeOut(back(1.4))`
- Bridge label type: `linear`
- Accent line extend: `easeOut(cubic)`
- Panel breathing glow: `easeInOut(sine)` (looping, 90-frame cycle)

## Narration Sync
> "The chip industry's answer wasn't 'review harder.' It was: verify the output against the spec. Review the Verilog, not the gates. That's what tests do for generated code."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  {/* Diff Fade Out */}
  <Sequence from={0} durationInFrames={30}>
    <FadeOut />
  </Sequence>

  {/* Divider */}
  <Sequence from={30} durationInFrames={30}>
    <VerticalDivider x={960} fromY={120} toY={800} color="rgba(255,255,255,0.08)" />
  </Sequence>

  {/* Left Panel — Prompt Document */}
  <Sequence from={60} durationInFrames={100}>
    <PromptDocument
      x={480} y={440} width={500} height={520}
      header="prompt.md"
      borderColor="#D9944A"
      lineCount={12}
      glowColor="rgba(217,148,74,0.08)"
    />
    <SubLabel text="30 lines · Reviewable" x={480} y={760} color="#D9944A" />
  </Sequence>

  {/* Right Panel — Test Suite */}
  <Sequence from={90} durationInFrames={110}>
    <TestSuitePanel
      x={1440} y={440} width={500} height={520}
      header="tests/"
      borderColor="#2AA198"
      tests={[
        "test_handles_null_input",
        "test_unicode_output",
        "test_empty_string",
        "test_large_payload",
        "test_concurrent_access",
        "test_error_recovery",
        "test_edge_case_zero",
        "test_integration_roundtrip"
      ]}
    />
    <SubLabel text="8 tests · All passing" x={1440} y={760} color="#2AA198" />
  </Sequence>

  {/* Bridge Label */}
  <Sequence from={200} durationInFrames={60}>
    <BridgeLabel
      text="Review the spec. Verify the output."
      x={960} y={860}
      accentLineWidth={120}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "divider": {
    "x": 960,
    "fromY": 120,
    "toY": 800,
    "color": "rgba(255,255,255,0.08)"
  },
  "promptDocument": {
    "position": { "x": 480, "y": 440 },
    "size": { "width": 500, "height": 520 },
    "header": "prompt.md",
    "borderColor": "#D9944A",
    "fillColor": "rgba(217,148,74,0.04)",
    "headerFill": "rgba(217,148,74,0.1)",
    "lineCount": 12,
    "glowColor": "rgba(217,148,74,0.08)",
    "subLabel": "30 lines · Reviewable"
  },
  "testSuite": {
    "position": { "x": 1440, "y": 440 },
    "size": { "width": 500, "height": 520 },
    "header": "tests/",
    "borderColor": "#2AA198",
    "fillColor": "rgba(42,161,152,0.04)",
    "headerFill": "rgba(42,161,152,0.1)",
    "checkmarkColor": "#2AA198",
    "tests": [
      "test_handles_null_input",
      "test_unicode_output",
      "test_empty_string",
      "test_large_payload",
      "test_concurrent_access",
      "test_error_recovery",
      "test_edge_case_zero",
      "test_integration_roundtrip"
    ],
    "subLabel": "8 tests · All passing"
  },
  "bridgeLabel": {
    "text": "Review the spec. Verify the output.",
    "position": { "x": 960, "y": 860 },
    "accentLineWidth": 120,
    "accentColor": "rgba(255,255,255,0.2)"
  }
}
```

---
