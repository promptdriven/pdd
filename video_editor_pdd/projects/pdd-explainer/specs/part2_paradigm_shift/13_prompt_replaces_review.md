[Remotion]

# Section 2.13: Prompt Replaces Review — Spec + Tests as the New Verification

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 3:35 - 3:49

## Visual Description

The overwhelming code diff from the previous spec dissolves. In its place, a clean composition appears: a compact, readable prompt document on the left and a test suite with green checkmarks on the right. Below them, a label reads: "Review the spec. Verify the output."

Then a morphing animation closes the section: the prompt document pulses, and code flows out of it, filling a defined shape like liquid in a mold. Test walls appear around the code, constraining it. The final frame is the complete PDD picture — prompt as mold, tests as walls, code as disposable output.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Prompt Document (left)
- Position: x: 300, y: 300, width: 400, height: 350
- Background: `#0F172A` at 0.9, 1px border `#4ADE80` at 0.4, border-radius 8px
- Glow: `#4ADE80` at 0.06, blur 20px
- Header: "PROMPT" — Inter, 14px, bold, `#4ADE80` at 0.7
- Content: 6-8 lines of readable natural language (placeholder text), Inter, 12px, `#E2E8F0` at 0.6
- File icon in corner: `#4ADE80` at 0.3

#### Test Suite (right)
- Position: x: 1220, y: 300, width: 400, height: 350
- Background: `#0F172A` at 0.9, 1px border `#334155` at 0.3, border-radius 8px
- Header: "TESTS" — Inter, 14px, bold, `#4ADE80` at 0.7
- Test items: 6 rows, each with green checkmark `#4ADE80` and test name in `#94A3B8`
  - "test_null_input ✓"
  - "test_unicode_handling ✓"
  - "test_max_length ✓"
  - "test_injection_safe ✓"
  - "test_performance_bound ✓"
  - "test_empty_string ✓"
- Font: JetBrains Mono, 11px

#### Label
- "Review the spec. Verify the output." — Inter, 22px, semi-bold (600), `#E2E8F0`
- Centered at (960, 740)

#### Mold Animation (Phase 2)
- Prompt document pulses and shrinks to left-center
- Code lines flow out from the right edge of the prompt, streaming rightward
- Code: horizontal lines of varying length, `#94A3B8` at 0.3, growing from the prompt
- Test walls: vertical barriers appear from top and bottom, `#D9944A` at 0.5, 3px
- The code fills the space between the walls — constrained by tests
- Final state: prompt → flowing code → test walls = the mold metaphor realized

### Animation Sequence
1. **Frame 0-60 (0-2s):** Previous code diff dissolves (fade out with slight blur). Clean background.
2. **Frame 60-150 (2-5s):** Prompt document slides in from left. Readable natural language content types on. Glow appears.
3. **Frame 150-240 (5-8s):** Test suite slides in from right. Checkmarks appear one by one, staggered.
4. **Frame 240-300 (8-10s):** Label fades in: "Review the spec. Verify the output." Hold.
5. **Frame 300-330 (10-11s):** Scene transitions. Prompt and tests reposition — prompt to far left, tests become wall segments flanking a central area.
6. **Frame 330-390 (11-13s):** Prompt pulses. Code streams out of it, flowing right, filling the space between test walls. The mold metaphor is complete.
7. **Frame 390-420 (13-14s):** Final hold. Prompt glows, code fills the mold, test walls constrain. The image is the thesis.

### Typography
- Prompt header: Inter, 14px, bold (700), `#4ADE80` at 0.7
- Prompt content: Inter, 12px, `#E2E8F0` at 0.6
- Test header: Inter, 14px, bold (700), `#4ADE80` at 0.7
- Test items: JetBrains Mono, 11px, `#94A3B8` at 0.6
- Checkmarks: `#4ADE80`
- Label: Inter, 22px, semi-bold (600), `#E2E8F0`

### Easing
- Diff dissolve: `easeOut(quad)` over 30 frames
- Document slide-in: `easeOut(cubic)` over 25 frames
- Checkmark stagger: `easeOut(back)` 5 frames apart — slight bounce
- Label fade-in: `easeOut(quad)` over 20 frames
- Scene transition: `easeInOut(cubic)` over 30 frames
- Code stream: `easeOut(quad)` per line, staggered 3 frames
- Test wall rise: `easeOut(cubic)` over 20 frames
- Prompt pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "Today, a modern chip has billions of gates. Nobody reviews the netlist. It's impossible. The abstraction isn't just convenient — it's physically necessary."

Segment: `part2_paradigm_shift_019` (continued)

- **3:35** (continuation): Code diff dissolves, clean prompt + tests appear
- **3:40** ("Review the spec"): Label appears
- **3:45** (end of narration): Mold animation — prompt → code → test walls

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Phase 1: Prompt + Tests side by side */}
    <Sequence from={60}>
      <SlideIn from="left" distance={40} duration={25}>
        <PromptDocument
          x={300} y={300} width={400} height={350}
          header="PROMPT"
          content={PROMPT_CONTENT}
          glowColor="#4ADE80" glowOpacity={0.06}
          borderColor="#4ADE80" />
      </SlideIn>
    </Sequence>

    <Sequence from={150}>
      <SlideIn from="right" distance={40} duration={25}>
        <TestSuite
          x={1220} y={300} width={400} height={350}
          header="TESTS"
          tests={[
            'test_null_input',
            'test_unicode_handling',
            'test_max_length',
            'test_injection_safe',
            'test_performance_bound',
            'test_empty_string'
          ]}
          checkColor="#4ADE80"
          stagger={5} />
      </SlideIn>
    </Sequence>

    {/* Label */}
    <Sequence from={240}>
      <FadeIn duration={20}>
        <Text text="Review the spec. Verify the output."
          font="Inter" size={22} weight={600}
          color="#E2E8F0"
          x={960} y={740} align="center" />
      </FadeIn>
    </Sequence>

    {/* Phase 2: Mold animation */}
    <Sequence from={300}>
      <MoldAnimation
        promptPosition={[200, 400]}
        codeStreamDirection="right"
        codeColor="#94A3B8" codeOpacity={0.3}
        wallColor="#D9944A" wallOpacity={0.5}
        wallWidth={3}
        promptPulse={{ color: '#4ADE80', cycle: 30 }}
        transitionDuration={30}
        streamStagger={3} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "prompt_replaces_review",
  "phases": [
    {
      "id": "spec_and_tests",
      "elements": ["prompt_document", "test_suite", "review_label"]
    },
    {
      "id": "mold_metaphor",
      "elements": ["prompt_source", "code_stream", "test_walls"]
    }
  ],
  "promptDocument": {
    "label": "PROMPT",
    "glowColor": "#4ADE80",
    "lineCount": 8
  },
  "testSuite": {
    "label": "TESTS",
    "testCount": 6,
    "checkColor": "#4ADE80"
  },
  "reviewLabel": "Review the spec. Verify the output.",
  "moldAnimation": {
    "codeColor": "#94A3B8",
    "wallColor": "#D9944A"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part2_paradigm_shift_019"]
}
```

---
