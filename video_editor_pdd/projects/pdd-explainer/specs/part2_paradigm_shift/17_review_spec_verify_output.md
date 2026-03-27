[Remotion]

# Section 2.17: Review the Spec, Verify the Output

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 3:35 - 3:47

## Visual Description

The overwhelming code diff dissolves. In its place, two clean elements appear side by side:

**LEFT:** A compact prompt document — readable, structured, ~20 lines of clear natural language. Warm amber glow around it. The prompt is legible and reviewable.

**RIGHT:** A test suite panel with green checkmarks. Five test names, each with a green check. The tests are the verification layer — they prove the output matches the spec without requiring line-by-line code review.

A label appears below: "Review the spec. Verify the output." This is the chip industry's answer applied to software.

The visual then morphs: the Verilog code (from earlier) transforms into the glowing prompt document. The gate-level netlist transforms into lines of software code. The Synopsys checkmark transforms into the test suite with green checks. The structural parallel is made visually explicit through animation.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid: Faint blueprint grid, `#1E293B` at 0.03

### Chart/Visual Elements

#### Prompt Document (left)
- Container: `#1E293B` background, rounded corners 8px, 24px padding
- Text: Inter, 14px, `#E2E8F0`, 20 lines of readable prompt text
- Aura: `#D9944A` glow at 0.15, 20px blur radius
- Position: x: 200, y: 200, width: 650px
- Header: "PROMPT" — Inter, 12px, bold, `#D9944A`, letter-spacing 3px

#### Test Suite (right)
- Container: `#1E293B` background, rounded corners 8px, 24px padding
- 5 test rows, each with:
  - Green checkmark: `#5AAA6E`, 20px
  - Test name: JetBrains Mono, 14px, `#E2E8F0`
  - "PASS": JetBrains Mono, 12px, `#5AAA6E`
- Position: x: 1050, y: 200, width: 650px
- Header: "TEST SUITE" — Inter, 12px, bold, `#5AAA6E`, letter-spacing 3px

#### Label
- "Review the spec. Verify the output." — Inter, 24px, bold, `#E2E8F0`, centered at y: 850
- Underline: `#5AAA6E`, 2px, drawing from center

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Code diff dissolves (particle scatter). Clean dark background.
2. **Frame 45-105 (1.5-3.5s):** Prompt document fades in from left. "PROMPT" header appears. Lines of text populate. Amber aura builds.
3. **Frame 105-180 (3.5-6s):** Test suite fades in from right. "TEST SUITE" header appears. Test rows populate one by one. Each checkmark bounces in green.
4. **Frame 180-240 (6-8s):** Label types in: "Review the spec. Verify the output." Underline draws.
5. **Frame 240-270 (8-9s):** Morph begins. Prompt document smoothly transforms — text rearranges to suggest Verilog→Prompt transition.
6. **Frame 270-330 (9-11s):** Test checkmarks morph and rearrange, suggesting the structural parallel with Synopsys verification.
7. **Frame 330-360 (11-12s):** Hold. Both panels stable. The parallel is complete.

### Typography
- Headers: Inter, 12px, bold (700), respective accent colors, letter-spacing 3px
- Prompt text: Inter, 14px, regular (400), `#E2E8F0`
- Test names: JetBrains Mono, 14px, regular (400), `#E2E8F0`
- Pass labels: JetBrains Mono, 12px, bold (700), `#5AAA6E`
- Bottom label: Inter, 24px, bold (700), `#E2E8F0`

### Easing
- Diff dissolve: `easeIn(quad)` over 45 frames
- Panel fade-in: `easeOut(cubic)` over 30 frames
- Checkmark bounce: `easeOut(back)` with overshoot 1.3
- Label type-in: linear, 2 frames per character
- Underline draw: `easeInOut(cubic)` over 20 frames
- Morph transitions: `easeInOut(cubic)` over 60 frames

## Narration Sync
> "The chip industry's answer wasn't 'review harder.' It was: verify the output against the spec. Review the Verilog, not the gates. That's what tests do for generated code."
> "This is that same transition. For software."

Segments: `part2_paradigm_shift_016` (tail — implied continuation)

- **228.0s**: Diff dissolves
- **230.0s**: Prompt document appears — "verify the output against the spec"
- **233.0s**: Test suite appears — "That's what tests do"
- **236.0s**: Label appears — "Review the spec. Verify the output."
- **239.0s**: Morph — "This is that same transition. For software."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.03} />

    {/* Diff dissolve */}
    <Sequence from={0} durationInFrames={45}>
      <ParticleDissolve duration={45}>
        <CodeDiffSnapshot />
      </ParticleDissolve>
    </Sequence>

    {/* Prompt document */}
    <Sequence from={45}>
      <FadeIn duration={30}>
        <PromptDocument
          header="PROMPT" headerColor="#D9944A"
          lines={promptLines} textColor="#E2E8F0"
          auraColor="#D9944A" auraOpacity={0.15}
          x={200} y={200} width={650}
        />
      </FadeIn>
    </Sequence>

    {/* Test suite */}
    <Sequence from={105}>
      <FadeIn duration={30}>
        <TestSuitePanel
          header="TEST SUITE" headerColor="#5AAA6E"
          tests={testResults}
          checkColor="#5AAA6E" textColor="#E2E8F0"
          x={1050} y={200} width={650}
        />
      </FadeIn>
    </Sequence>

    {/* Bottom label */}
    <Sequence from={180}>
      <TypeWriter
        text="Review the spec. Verify the output."
        font="Inter" size={24} weight={700}
        color="#E2E8F0" charDelay={2}
        x={960} y={850} align="center"
      />
      <Sequence from={40}>
        <DrawLine from={[760, 880]} to={[1160, 880]}
          color="#5AAA6E" width={2} drawDuration={20} fromCenter />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "comparison_layout",
  "chartId": "review_spec_verify_output",
  "panels": {
    "left": {
      "type": "prompt_document",
      "header": "PROMPT",
      "accentColor": "#D9944A",
      "lineCount": 20
    },
    "right": {
      "type": "test_suite",
      "header": "TEST SUITE",
      "accentColor": "#5AAA6E",
      "tests": [
        { "name": "test_counter_increments", "status": "pass" },
        { "name": "test_reset_clears_state", "status": "pass" },
        { "name": "test_overflow_wraps", "status": "pass" },
        { "name": "test_edge_case_zero", "status": "pass" },
        { "name": "test_concurrent_access", "status": "pass" }
      ]
    }
  },
  "label": "Review the spec. Verify the output.",
  "narrationSegments": ["part2_paradigm_shift_016"]
}
```

---
