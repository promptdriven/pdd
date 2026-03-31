[Remotion]

# Section 0.11: Test Failure → Fix → Regenerate Cycle

**Tool:** Remotion
**Duration:** ~13s (390 frames @ 30fps)
**Timestamp:** 0:33 - 0:46

## Visual Description

The demo's payoff moment. Starting from the generated code visible in spec 10, a red test failure appears — a new test `test_unicode_domain` has been added and it fails. The failure is visible: red X, assertion error, expected vs. actual output.

Then the terminal runs `pdd fix email_validator`. The code REGENERATES (not patches — the whole file refreshes). All tests re-run. Green checkmarks cascade down the test list — every test passes, including the new one. The bug is not patched; it's gone. And the test is a permanent wall ensuring it can never return.

This is the "a-ha" moment: the test-fix-regenerate cycle that makes PDD fundamentally different from patching.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (GitHub dark theme)
- Layout: Code pane (left 55%) / Test results pane (right 45%)

### Chart/Visual Elements

#### Test Results Pane (right)
- Background: `#0D1117`
- Test list with status icons:
  - `✓ test_basic_email` — `#4ADE80` (green)
  - `✓ test_invalid_format` — `#4ADE80`
  - `✓ test_missing_domain` — `#4ADE80`
  - `✗ test_unicode_domain` — `#EF4444` (red), bold
  - Error details: `AssertionError: expected True, got False` in `#EF4444` at 0.7
- Font: JetBrains Mono, 14px

#### Failed Test Highlight
- Red border-left: 3px, `#EF4444`
- Red background glow: `#EF4444` at 0.05

#### Terminal Command
- `$ pdd fix email_validator` — types in after failure is shown
- Spinner animation: `⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏` cycling at 100ms
- Result: `✓ Fixed and regenerated (1.2s)` in `#4ADE80`

#### Regeneration Flash
- Brief white flash (`#FFFFFF` at 0.03) across code pane when regeneration occurs
- Code content refreshes — visibly different (cleaner handling of unicode section)

#### Re-run Results
- All tests re-run with cascade animation:
  - `✓ test_basic_email` — green
  - `✓ test_invalid_format` — green
  - `✓ test_missing_domain` — green
  - `✓ test_unicode_domain` — green (was red, now green)
- Each checkmark appears with a slight pop animation
- Bottom summary: `4/4 passed` in `#4ADE80`, bold

### Animation Sequence
1. **Frame 0-30 (0-1s):** Test results pane appears. First three tests pass (green checkmarks cascade). Fourth test (`test_unicode_domain`) fails — red X with error details.
2. **Frame 30-90 (1-3s):** Hold on failure. Red glow pulses on the failed test. Error details visible.
3. **Frame 90-120 (3-4s):** Terminal types `pdd fix email_validator`. Spinner starts.
4. **Frame 120-180 (4-6s):** Code pane flashes — regeneration in progress. Code content refreshes. Spinner continues.
5. **Frame 180-210 (6-7s):** Terminal shows success. `✓ Fixed and regenerated`.
6. **Frame 210-300 (7-10s):** Test results clear and re-run. All four tests pass — green checkmarks cascade down. The previously-failed test is now green.
7. **Frame 300-330 (10-11s):** "4/4 passed" summary fades in with subtle green glow.
8. **Frame 330-390 (11-13s):** Hold on all-green results. The permanence of the fix is clear.

### Typography
- Test names: JetBrains Mono, 14px, regular (400)
- Pass icon: `✓` in `#4ADE80`, bold
- Fail icon: `✗` in `#EF4444`, bold
- Error text: JetBrains Mono, 12px, `#EF4444` at 0.7
- Terminal: JetBrains Mono, 13px, `#94A3B8`
- Summary: JetBrains Mono, 16px, bold (700), `#4ADE80`

### Easing
- Checkmark cascade: `easeOut(back)` with 5-frame stagger
- Red glow pulse: `easeInOut(sine)` on 40-frame cycle
- Regeneration flash: `easeOut(quad)` over 8 frames
- Terminal type: linear, 2 frames per character
- Summary fade-in: `easeOut(quad)` over 15 frames

## Narration Sync
> "a failing test. Regenerate. Bug gone. Not patched — gone. The test is a permanent wall. That bug can never come back."

Segment: `cold_open_009`

- **32.88s** (seg 009): Test failure appears — "a failing test"
- **35.00s**: Terminal runs fix command — "Regenerate"
- **37.00s**: Code regenerates, tests re-run — "Bug gone"
- **39.00s**: All tests green — "Not patched — gone"
- **42.00s**: Hold on green results — "The test is a permanent wall"
- **45.74s** (seg 009 ends): "That bug can never come back"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={390}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Code pane (left) */}
    <Pane width="55%" side="left">
      <CodeBlock code={generatedCode} font="JetBrains Mono" size={14} />

      {/* Regeneration flash */}
      <Sequence from={120}>
        <Flash color="#FFFFFF" opacity={0.03} duration={8} />
        <CodeBlock code={regeneratedCode} font="JetBrains Mono" size={14} />
      </Sequence>
    </Pane>

    {/* Test results pane (right) */}
    <Pane width="45%" side="right">
      {/* Initial run with failure */}
      <Sequence from={0} durationInFrames={210}>
        <TestResultList
          results={[
            { name: "test_basic_email", status: "pass", delay: 0 },
            { name: "test_invalid_format", status: "pass", delay: 5 },
            { name: "test_missing_domain", status: "pass", delay: 10 },
            { name: "test_unicode_domain", status: "fail", delay: 15,
              error: "AssertionError: expected True, got False" }
          ]}
          font="JetBrains Mono" size={14}
        />
      </Sequence>

      {/* Re-run with all passing */}
      <Sequence from={210}>
        <TestResultList
          results={[
            { name: "test_basic_email", status: "pass", delay: 0 },
            { name: "test_invalid_format", status: "pass", delay: 5 },
            { name: "test_missing_domain", status: "pass", delay: 10 },
            { name: "test_unicode_domain", status: "pass", delay: 15 }
          ]}
          font="JetBrains Mono" size={14}
        />
        <Sequence from={90}>
          <FadeIn duration={15}>
            <Badge text="4/4 passed" color="#4ADE80"
              position={{ x: "center", y: 500 }} />
          </FadeIn>
        </Sequence>
      </Sequence>
    </Pane>

    {/* Terminal bar */}
    <Sequence from={90}>
      <TerminalBar
        command="pdd fix email_validator"
        spinner={true}
        result="✓ Fixed and regenerated (1.2s)"
        resultColor="#4ADE80"
        typeDelay={2}
        spinnerDuration={90}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "test_fix_cycle",
  "tests": [
    { "name": "test_basic_email", "initialStatus": "pass", "finalStatus": "pass" },
    { "name": "test_invalid_format", "initialStatus": "pass", "finalStatus": "pass" },
    { "name": "test_missing_domain", "initialStatus": "pass", "finalStatus": "pass" },
    { "name": "test_unicode_domain", "initialStatus": "fail", "finalStatus": "pass" }
  ],
  "terminal": {
    "command": "pdd fix email_validator",
    "result": "Fixed and regenerated (1.2s)"
  },
  "keyInsight": "Bug is gone, not patched. Test is a permanent wall.",
  "narrationSegments": ["cold_open_009"]
}
```

---
