[Remotion]

# Section 0.9: Test Fix Cycle — Red to Green

**Tool:** Remotion
**Duration:** ~13s (390 frames @ 30fps)
**Timestamp:** 0:32 - 0:45

## Visual Description

The PDD feedback loop in action. The screen is split into two vertical zones: a code editor on the left showing the generated `email_validator.py`, and a test runner terminal on the right.

A red test failure appears in the terminal: `FAIL test_email_validator.py::test_unicode_domain`. The failure message is visible — an `AssertionError` with a clear mismatch. Then a new test is added: `test_unicode_domain` appears in the editor, highlighted in yellow as a new addition.

The terminal runs `$ pdd fix email_validator`. The code in the left panel shimmers — a regeneration effect ripples through the file (the entire module regenerates, not just a patch). When it settles, the test runner fires again. Tests scroll by — all green checkmarks. The final line: `5 passed ✓` in bright green. The transition from red failure to green success is visceral and satisfying.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy)
- Layout: 55/45 split — code editor (left, 1040px), terminal (right, 840px), 40px gap

### Chart/Visual Elements

#### Code Editor (Left Panel)
- Background: `#1E1E2E`, 8px border-radius
- Title bar: `email_validator.py` in `#CDD6F4`
- Code: Python, JetBrains Mono 12px, Catppuccin Mocha syntax colors
- ~25 lines visible (the clean generated code from spec 08)
- New test highlight: `#F9E2AF` at 0.15 background on the `test_unicode_domain` function

#### Test Runner Terminal (Right Panel)
- Background: `#11111B`, 8px border-radius
- Title: `pytest` in `#94A3B8`
- Failed test: `FAIL` in `#F38BA8` (red), test name in `#CDD6F4`
- Error trace: `#F38BA8` at 0.7, indented, 3-4 lines
- `pdd fix` command: `#94A3B8`
- Passing tests: Each line prefixed with `✓` in `#A6E3A1` (green)
- Final summary: `5 passed` in `#A6E3A1`, bold

#### Regeneration Effect
- When `pdd fix` runs, the code editor shimmers: a horizontal wave of `#89B4FA` at 0.1 sweeps top-to-bottom
- Code text briefly fades to 0.3 opacity and back — the content changes during the fade
- Effect duration: ~45 frames (1.5s)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Layout fades in. Code editor on left shows clean `email_validator.py`. Terminal on right is empty with cursor.
2. **Frame 30-60 (1-2s):** Terminal: `$ pytest test_email_validator.py` types in. Runs.
3. **Frame 60-100 (2-3.3s):** Red failure appears: `FAIL test_unicode_domain`. Error trace prints. Red `✗` icon.
4. **Frame 100-130 (3.3-4.3s):** New test `test_unicode_domain` highlights in the code editor. Yellow glow on the new lines.
5. **Frame 130-160 (4.3-5.3s):** Terminal: `$ pdd fix email_validator` types in.
6. **Frame 160-210 (5.3-7s):** Regeneration shimmer effect on the code editor. Code fades, refreshes, returns. The module is rewritten.
7. **Frame 210-250 (7-8.3s):** Terminal: `$ pytest test_email_validator.py` runs again automatically.
8. **Frame 250-340 (8.3-11.3s):** Tests scroll by — one by one, each with a green `✓`. Five tests total: `test_basic_format ✓`, `test_invalid_domain ✓`, `test_empty_string ✓`, `test_special_chars ✓`, `test_unicode_domain ✓`. Each appears with a satisfying beat.
9. **Frame 340-370 (11.3-12.3s):** Summary line: `5 passed ✓` in bold green. The terminal glows subtly.
10. **Frame 370-390 (12.3-13s):** Hold on the green result. Beat.

### Typography
- Code: JetBrains Mono, 12px, syntax colors
- Terminal command: JetBrains Mono, 13px, `#94A3B8`
- Test results: JetBrains Mono, 13px, `#A6E3A1` (pass) / `#F38BA8` (fail)
- Summary: JetBrains Mono, 14px, bold, `#A6E3A1`
- Error trace: JetBrains Mono, 11px, `#F38BA8` at 0.7

### Easing
- Layout fade-in: `easeOut(quad)` over 20 frames
- Red failure appear: `easeOut(quad)` over 10 frames
- New test highlight: `easeOut(quad)` over 15 frames, yellow glow pulse
- Regeneration shimmer: `easeInOut(sine)` sweep over 45 frames
- Green checkmark appear: `easeOut(back)` over 8 frames each (slight overshoot)
- Summary glow: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "a failing test. Regenerate. Bug fixed. All tests pass. No patch. No diff. Just regenerate from the prompt."

Segment: `cold_open_009`

- **32.88s** (seg 009): Layout appears — "a failing test"
- **34.5s**: Red failure visible
- **36.0s**: "Regenerate" — `pdd fix` runs, shimmer effect
- **38.0s**: "Bug fixed" — code refreshes
- **40.0s**: "All tests pass" — green checkmarks scrolling
- **43.0s**: "No patch. No diff." — hold on green summary
- **45.74s** (seg 009 ends): Beat on clean result

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={390}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Two-panel layout */}
    <TwoPanelLayout leftWidth={1040} rightWidth={840} gap={40}>
      {/* Left: Code Editor */}
      <CodeEditorPanel>
        <CodeEditorChrome filename="email_validator.py" theme="catppuccin-mocha" />
        <CodeBlock code={EMAIL_VALIDATOR_CODE} language="python" />

        {/* New test highlight */}
        <Sequence from={100} durationInFrames={60}>
          <LineHighlight
            startLine={22} endLine={28}
            color="#F9E2AF" opacity={0.15}
            easing="easeOutQuad"
          />
        </Sequence>

        {/* Regeneration shimmer */}
        <Sequence from={160} durationInFrames={50}>
          <ShimmerEffect
            color="#89B4FA" opacity={0.1}
            direction="top-to-bottom"
            durationFrames={45}
          />
          <CodeSwap
            from={EMAIL_VALIDATOR_V1}
            to={EMAIL_VALIDATOR_V2}
            fadeFrames={20}
          />
        </Sequence>
      </CodeEditorPanel>

      {/* Right: Terminal */}
      <TerminalPanel background="#11111B">
        {/* First test run - failure */}
        <Sequence from={30} durationInFrames={70}>
          <TypewriterCommand command="pytest test_email_validator.py" />
        </Sequence>
        <Sequence from={60} durationInFrames={40}>
          <TestFailure
            testName="test_unicode_domain"
            error="AssertionError: Expected valid=True for 'user@münchen.de'"
            color="#F38BA8"
          />
        </Sequence>

        {/* Fix command */}
        <Sequence from={130} durationInFrames={30}>
          <TypewriterCommand command="pdd fix email_validator" />
        </Sequence>

        {/* Second test run - all pass */}
        <Sequence from={210} durationInFrames={40}>
          <TypewriterCommand command="pytest test_email_validator.py" />
        </Sequence>
        <Sequence from={250} durationInFrames={90}>
          {TEST_RESULTS.map((test, i) => (
            <Sequence key={i} from={i * 18} durationInFrames={18}>
              <TestPass name={test} easing="easeOutBack" />
            </Sequence>
          ))}
        </Sequence>
        <Sequence from={340} durationInFrames={50}>
          <TestSummary passed={5} color="#A6E3A1" glow />
        </Sequence>
      </TerminalPanel>
    </TwoPanelLayout>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "remotion_animation",
  "componentId": "test_fix_cycle",
  "durationFrames": 390,
  "fps": 30,
  "narrationSegments": ["cold_open_009"],
  "phases": ["initial_failure", "add_test", "pdd_fix", "regenerate", "all_pass"],
  "failingTest": "test_unicode_domain",
  "pddCommand": "pdd fix email_validator",
  "testResults": [
    "test_basic_format",
    "test_invalid_domain",
    "test_empty_string",
    "test_special_chars",
    "test_unicode_domain"
  ],
  "totalPassed": 5
}
```

---
