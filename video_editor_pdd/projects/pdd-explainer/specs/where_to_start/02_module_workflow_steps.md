[Remotion]

# Section 6.2: Module Workflow Steps — Terminal Walkthrough

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 23:19 - 23:31

## Visual Description

A terminal-style animation walks through four concrete steps of adopting PDD for a single existing module. The terminal window sits centered on a dark background, styled as a realistic developer console with a title bar ("~/project $"). Each step types out as a command, pauses, then receives a green checkmark confirming completion. The commands are:

1. `pdd generate auth_module` — generates a prompt from existing code
2. `vim specs/auth_module.md  # add tests` — user edits the spec to add tests
3. `pdd regenerate auth_module` — regenerates the module from the prompt
4. `diff auth_module.py auth_module_regen.py` — compares original vs regenerated

After all four steps complete, a summary line types out below: "All tests passing. Prompt is now source of truth." — rendered in gold to mark the milestone. The sequential, concrete framing makes PDD adoption feel approachable and non-intimidating.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Terminal Window
- Position: centered at (960, 500), 900w × 500h
- Title bar: 900w × 32h, `#1E293B`, rounded top corners 8px
- Title bar dots: three circles 10px, `#EF4444` at 0.6, `#FBBF24` at 0.6, `#5AAA6E` at 0.6, left-aligned 16px from left
- Title text: "~/project $" — JetBrains Mono, 11px, `#64748B` at 0.5, right of dots
- Body: 900w × 468h, `#0F172A`, 1px `#1E293B` border, rounded bottom corners 8px

#### Step Lines (inside terminal body)
- Each step occupies ~90px vertical space
- Prompt: "$ " — JetBrains Mono, 14px, `#5AAA6E` at 0.7
- Command text: JetBrains Mono, 14px, `#E2E8F0`
- Comment text: JetBrains Mono, 14px, `#64748B` at 0.5
- Checkmark: "✓" — JetBrains Mono, 16px, `#5AAA6E`, appears after command completes
- Step positions (y from top of body): Step 1: y=80, Step 2: y=160, Step 3: y=240, Step 4: y=320

#### Step 1
- Command: `pdd generate auth_module`
- Output (dimmed): "→ Generated specs/auth_module.md from auth_module.py" — 12px, `#94A3B8` at 0.4

#### Step 2
- Command: `vim specs/auth_module.md  # add tests`

#### Step 3
- Command: `pdd regenerate auth_module`
- Output (dimmed): "→ Regenerated auth_module.py (14 tests passing)" — 12px, `#94A3B8` at 0.4

#### Step 4
- Command: `diff auth_module.py auth_module_regen.py`
- Output (dimmed): "→ 3 lines changed, all behavior preserved" — 12px, `#94A3B8` at 0.4

#### Summary Line
- Position: y=410 inside terminal body
- Text: "All tests passing. Prompt is now source of truth." — JetBrains Mono, 14px, bold (700), `#FBBF24`
- Underline: 420px, 2px, `#FBBF24` at 0.3

### Animation Sequence
1. **Frame 0-30 (0-1s):** Terminal window fades in with subtle scale 0.95→1.0. Title bar appears.
2. **Frame 30-90 (1-3s):** Step 1 types out character-by-character (~40ms/char). Checkmark appears with pop. Output line fades in.
3. **Frame 90-150 (3-5s):** Step 2 types out. Comment text in dimmer color. Checkmark pops.
4. **Frame 150-225 (5-7.5s):** Step 3 types out. Output shows "14 tests passing" — the "14" flashes green. Checkmark pops.
5. **Frame 225-290 (7.5-9.67s):** Step 4 types out. Diff output appears. Checkmark pops.
6. **Frame 290-340 (9.67-11.33s):** Summary line types out in gold. Underline draws left-to-right.
7. **Frame 340-360 (11.33-12s):** Hold. Subtle golden glow pulses once on summary text.

### Typography
- Terminal title: JetBrains Mono, 11px, `#64748B` at 0.5
- Prompt prefix: JetBrains Mono, 14px, `#5AAA6E` at 0.7
- Command text: JetBrains Mono, 14px, `#E2E8F0`
- Comment text: JetBrains Mono, 14px, `#64748B` at 0.5
- Output text: JetBrains Mono, 12px, `#94A3B8` at 0.4
- Summary: JetBrains Mono, 14px, bold (700), `#FBBF24`

### Easing
- Terminal fade-in: `easeOut(cubic)` scale 0.95→1.0 over 25 frames
- Character typing: linear, ~40ms per character
- Checkmark pop: `easeOut(back(1.5))` scale 0→1 over 10 frames
- Output fade: `easeOut(quad)` over 15 frames
- Summary type: linear, ~50ms per character (slightly slower for emphasis)
- Summary underline: `easeInOut(cubic)` over 20 frames
- Golden glow: `easeInOut(sine)` opacity 0→0.2→0, 15 frames

## Narration Sync
> "Start with one module. Generate its prompt. Add tests. Regenerate. Compare."

Segment: `where_to_start_001`

- **23:19** ("Start with one module"): Terminal fades in, Step 1 begins typing
- **23:21** ("Generate its prompt"): Step 1 completes, checkmark appears
- **23:23** ("Add tests"): Step 2 types out
- **23:25** ("Regenerate"): Step 3 types out with test passing output
- **23:27** ("Compare"): Step 4 types out with diff output

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Terminal window */}
    <Sequence from={0}>
      <ScaleFadeIn from={0.95} to={1.0} duration={25}>
        <TerminalWindow x={510} y={250} width={900} height={500}
          titleBarColor="#1E293B" bodyColor="#0F172A"
          title="~/project $" />
      </ScaleFadeIn>
    </Sequence>

    {/* Step 1: generate */}
    <Sequence from={30}>
      <TypewriterLine prompt="$ " text="pdd generate auth_module"
        charDelay={40} font="JetBrains Mono" size={14}
        promptColor="#5AAA6E" textColor="#E2E8F0"
        y={330} />
      <Sequence from={50}>
        <CheckmarkPop color="#5AAA6E" size={16} />
        <FadeIn duration={15}>
          <Text text="→ Generated specs/auth_module.md from auth_module.py"
            font="JetBrains Mono" size={12}
            color="#94A3B8" opacity={0.4} y={354} />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Step 2: add tests */}
    <Sequence from={90}>
      <TypewriterLine prompt="$ " text="vim specs/auth_module.md"
        comment="  # add tests"
        charDelay={40} font="JetBrains Mono" size={14}
        promptColor="#5AAA6E" textColor="#E2E8F0"
        commentColor="#64748B" y={410} />
      <Sequence from={50}>
        <CheckmarkPop color="#5AAA6E" size={16} />
      </Sequence>
    </Sequence>

    {/* Step 3: regenerate */}
    <Sequence from={150}>
      <TypewriterLine prompt="$ " text="pdd regenerate auth_module"
        charDelay={40} font="JetBrains Mono" size={14}
        promptColor="#5AAA6E" textColor="#E2E8F0"
        y={490} />
      <Sequence from={60}>
        <CheckmarkPop color="#5AAA6E" size={16} />
        <FadeIn duration={15}>
          <Text text="→ Regenerated auth_module.py (14 tests passing)"
            font="JetBrains Mono" size={12}
            color="#94A3B8" opacity={0.4} y={514} />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Step 4: diff */}
    <Sequence from={225}>
      <TypewriterLine prompt="$ "
        text="diff auth_module.py auth_module_regen.py"
        charDelay={40} font="JetBrains Mono" size={14}
        promptColor="#5AAA6E" textColor="#E2E8F0"
        y={570} />
      <Sequence from={55}>
        <CheckmarkPop color="#5AAA6E" size={16} />
        <FadeIn duration={15}>
          <Text text="→ 3 lines changed, all behavior preserved"
            font="JetBrains Mono" size={12}
            color="#94A3B8" opacity={0.4} y={594} />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Summary line */}
    <Sequence from={290}>
      <TypewriterLine text="All tests passing. Prompt is now source of truth."
        charDelay={50} font="JetBrains Mono" size={14}
        weight={700} textColor="#FBBF24" y={660} />
      <Sequence from={40}>
        <LineDraw from={[510, 678]} to={[930, 678]}
          color="#FBBF24" opacity={0.3} width={2} duration={20} />
      </Sequence>
      <Sequence from={50}>
        <GlowPulse color="#FBBF24" blur={12} opacity={0.2}
          duration={15} />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_terminal",
  "terminalId": "module_workflow_steps",
  "steps": [
    {
      "command": "pdd generate auth_module",
      "output": "Generated specs/auth_module.md from auth_module.py",
      "step": 1
    },
    {
      "command": "vim specs/auth_module.md  # add tests",
      "output": null,
      "step": 2
    },
    {
      "command": "pdd regenerate auth_module",
      "output": "Regenerated auth_module.py (14 tests passing)",
      "step": 3
    },
    {
      "command": "diff auth_module.py auth_module_regen.py",
      "output": "3 lines changed, all behavior preserved",
      "step": 4
    }
  ],
  "summary": "All tests passing. Prompt is now source of truth.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_001"]
}
```

---
