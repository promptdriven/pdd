[split:]

# Section 2.11: Prompt Replaces Review — Spec + Tests vs. Code Review

**Tool:** Split
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 10:27 - 10:39

## Visual Description

A vertical split screen contrasting the old approach (review the code) with the new approach (review the spec, verify the output). This is the chip industry's answer applied to software.

**LEFT panel (labeled "OLD: Review the Code"):** The overwhelming code diff from the previous scene, still scrolling but now frozen and faded. A giant red question mark overlays it, pulsing. The message: this is what you're trying to do, and it's impossible. A small exhausted-face emoji (optional: just a wilting meter bar) at the bottom shows "Reviewer cognitive load: MAX."

**RIGHT panel (labeled "NEW: Review the Spec"):** A clean, compact prompt document (readable — maybe 15-20 lines) sits at top. Below it, a test suite panel shows green checkmarks ticking down a list. Everything is legible, manageable, human-scale. A small healthy meter bar at the bottom: "Reviewer cognitive load: LOW."

The contrast makes the argument: the chip industry's answer wasn't "review harder." It was: verify the output against the spec. Review the Verilog, not the gates.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x=960, color `#334155` at 0.25

### Chart/Visual Elements

#### Panel Headers
- LEFT: "REVIEW THE CODE" — Inter, 14px, semi-bold (600), `#EF4444` at 0.4, letter-spacing 2px, centered at y: 40, strikethrough line at 0.3
- RIGHT: "REVIEW THE SPEC" — Inter, 14px, semi-bold (600), `#5AAA6E` at 0.5, letter-spacing 2px, centered at y: 40

#### Left Panel — Old Approach (x: 0 to x: 958)
- Background: `#0F172A`
- **Frozen code diff:** Same diff content from previous scene, but static and faded
  - Overall opacity: 0.15 — barely legible, visually overwhelming
  - JetBrains Mono, 10px, muted colors
  - Fills the panel from y: 80 to y: 850
- **Red question mark overlay:**
  - Center: (480, 450), 200px tall
  - "?" — Inter, 200px, bold, `#EF4444` at 0.25, pulsing between 0.15 and 0.3
  - Glow: 30px Gaussian blur, `#EF4444` at 0.06
- **Cognitive load meter:**
  - Position: (480, 950), 300x16px
  - Bar: fully filled, `#EF4444` at 0.5
  - Label: "Cognitive load" — Inter, 10px, `#EF4444` at 0.4
  - Status: "OVERLOADED" — Inter, 10px, bold, `#EF4444` at 0.6

#### Right Panel — New Approach (x: 962 to x: 1920)
- Background: `#0A0F1A`
- **Prompt document** (upper portion):
  - Position: (1440, 280), 400x250px
  - Background: `#1E293B` at 0.3, 4px rounded corners
  - Header: "prompt.md" — JetBrains Mono, 10px, `#D9944A` at 0.4
  - Content: 12-15 lines of readable prompt text
    - Inter, 12px, `#E2E8F0` at 0.6
    - Key phrases highlighted in `#D9944A` at 0.5
  - Overall feel: compact, human-readable, manageable
- **Test suite panel** (lower portion):
  - Position: (1440, 650), 400x250px
  - Background: `#1E293B` at 0.2, 4px rounded corners
  - Header: "test_suite.py" — JetBrains Mono, 10px, `#5AAA6E` at 0.4
  - Test lines with green checkmarks:
    - "test_handles_null_input ✓"
    - "test_returns_correct_format ✓"
    - "test_unicode_support ✓"
    - "test_edge_case_empty ✓"
    - "test_performance_under_100ms ✓"
    - "test_idempotent_behavior ✓"
  - JetBrains Mono, 11px, `#5AAA6E` at 0.5
  - Checkmarks appear one by one
- **Cognitive load meter:**
  - Position: (1440, 950), 300x16px
  - Bar: ~25% filled, `#5AAA6E` at 0.5
  - Label: "Cognitive load" — Inter, 10px, `#5AAA6E` at 0.4
  - Status: "MANAGEABLE" — Inter, 10px, bold, `#5AAA6E` at 0.6

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split line draws. Panel headers fade in. LEFT header has strikethrough.
2. **Frame 20-60 (0.67-2s):** LEFT: Frozen code diff fades in at very low opacity. Overwhelming, unreadable. RIGHT: Prompt document fades in. Clean, readable.
3. **Frame 60-120 (2-4s):** LEFT: Red question mark fades in, begins pulsing. The impossibility. RIGHT: Prompt text is legible. A few key phrases highlight in amber.
4. **Frame 120-220 (4-7.33s):** RIGHT: Test suite panel appears. Checkmarks tick down the list, one every 15 frames. Green. Satisfying. Verified.
5. **Frame 220-280 (7.33-9.33s):** Both cognitive load meters appear. LEFT fills to 100% red. RIGHT fills to 25% green. The contrast in cognitive demand.
6. **Frame 280-360 (9.33-12s):** Hold. LEFT: overwhelming, unreadable, overloaded. RIGHT: clean, verified, manageable. The argument is made.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors, letter-spacing 2px
- Code diff: JetBrains Mono, 10px, `#94A3B8` at 0.15
- Prompt content: Inter, 12px, `#E2E8F0` at 0.6
- Test lines: JetBrains Mono, 11px, `#5AAA6E` at 0.5
- Meter labels: Inter, 10px, respective colors
- Meter status: Inter, 10px, bold, respective colors

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Code diff fade: `easeOut(quad)` over 20 frames
- Question mark pulse: `easeInOut(sine)` on 30-frame cycle
- Prompt fade: `easeOut(quad)` over 20 frames
- Checkmark tick: `easeOut(back(1.3))` scale pop, 8 frames each
- Meter fill: `easeOut(cubic)` over 30 frames
- Status label: `easeOut(quad)` over 15 frames

## Narration Sync
> "The chip industry's answer wasn't 'review harder.' It was: verify the output against the spec. Review the Verilog, not the gates. That's what tests do for generated code."

Segment: `part2_011`

- **10:27** ("The chip industry's answer wasn't 'review harder'"): Split appears, LEFT code diff overwhelming
- **10:31** ("verify the output against the spec"): RIGHT panel — prompt visible, readable
- **10:35** ("Review the Verilog, not the gates"): Test checkmarks ticking, cognitive load meters
- **10:38** ("That's what tests do for generated code"): Both panels complete, contrast held

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Old: Review the Code */}
    <Panel x={0} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
        <PanelHeader text="REVIEW THE CODE" color="#EF4444"
          opacity={0.4} letterSpacing={2} y={40}
          strikethrough />

        {/* Frozen code diff — faded, overwhelming */}
        <Sequence from={20}>
          <FadeIn duration={20}>
            <FrozenCodeDiff
              lines={diffLines} font="JetBrains Mono" size={10}
              opacity={0.15} region={[40, 80, 920, 850]}
            />
          </FadeIn>
        </Sequence>

        {/* Red question mark */}
        <Sequence from={60}>
          <PulsingText text="?" font="Inter" size={200}
            weight={700} color="#EF4444"
            baseOpacity={0.15} peakOpacity={0.3}
            pulsePeriod={30}
            x={480} y={450} align="center"
            glow={{ blur: 30, opacity: 0.06 }} />
        </Sequence>

        {/* Cognitive load meter */}
        <Sequence from={220}>
          <CognitiveLoadMeter
            position={[480, 950]} width={300}
            fillPercent={100} color="#EF4444"
            label="Cognitive load" status="OVERLOADED"
            fillDuration={30} />
        </Sequence>
      </AbsoluteFill>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.25}
      drawDuration={15} />

    {/* Right panel — New: Review the Spec */}
    <Panel x={962} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
        <PanelHeader text="REVIEW THE SPEC" color="#5AAA6E"
          opacity={0.5} letterSpacing={2} y={40} />

        {/* Prompt document */}
        <Sequence from={20}>
          <FadeIn duration={20}>
            <DocumentPanel
              title="prompt.md" titleColor="#D9944A"
              position={[480, 280]} width={400} height={250}
              content={promptText} font="Inter" size={12}
              color="#E2E8F0" opacity={0.6}
              highlightColor="#D9944A"
              bgColor="#1E293B" bgOpacity={0.3}
            />
          </FadeIn>
        </Sequence>

        {/* Test suite */}
        <Sequence from={120}>
          <TestSuitePanel
            title="test_suite.py" titleColor="#5AAA6E"
            position={[480, 650]} width={400} height={250}
            tests={testResults}
            font="JetBrains Mono" size={11}
            checkColor="#5AAA6E" checkInterval={15}
            bgColor="#1E293B" bgOpacity={0.2}
          />
        </Sequence>

        {/* Cognitive load meter */}
        <Sequence from={220}>
          <CognitiveLoadMeter
            position={[480, 950]} width={300}
            fillPercent={25} color="#5AAA6E"
            label="Cognitive load" status="MANAGEABLE"
            fillDuration={30} />
        </Sequence>
      </AbsoluteFill>
    </Panel>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_split",
  "splitPosition": 960,
  "leftPanel": {
    "label": "REVIEW THE CODE",
    "concept": "Impossible at scale — code review becomes netlist review",
    "cognitiveLoad": "OVERLOADED",
    "loadPercent": 100,
    "background": "#0F172A"
  },
  "rightPanel": {
    "label": "REVIEW THE SPEC",
    "concept": "Verify output against spec — review the prompt, run the tests",
    "cognitiveLoad": "MANAGEABLE",
    "loadPercent": 25,
    "tests": [
      "test_handles_null_input",
      "test_returns_correct_format",
      "test_unicode_support",
      "test_edge_case_empty",
      "test_performance_under_100ms",
      "test_idempotent_behavior"
    ],
    "background": "#0A0F1A"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["part2_011"]
}
```

---
