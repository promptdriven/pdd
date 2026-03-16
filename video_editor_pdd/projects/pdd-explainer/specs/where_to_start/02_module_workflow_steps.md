[Remotion]

# Section 6.2: Module Workflow — Four-Step Terminal Animation

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 22:24 - 22:36

## Visual Description
An animated terminal-style workflow showing the four concrete steps to start with PDD. A stylized dark terminal window occupies the center of the screen. Commands appear one at a time as typed text — each step lighting up in sequence: (1) pick a module, (2) generate its prompt, (3) add tests, (4) regenerate and compare. Each step gets a green checkmark when complete, building a visual checklist inside the terminal. The animation makes the abstract process tactile and actionable — a developer watching can picture themselves running these exact commands.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0A1628` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Terminal Window:** Centered at (960, 480), 900px wide x 500px tall
  - Background: `#111827`, border-radius 12px
  - Title bar: 36px tall, `#1E293B`, three dots (red `#EF4444`, yellow `#FBBF24`, green `#22C55E`) at 10px diameter, left-aligned at 16px
  - Title text: "pdd-workflow" — `#64748B`, 13px, JetBrains Mono, centered in title bar
- **Step 1 (Y=160 inside terminal):**
  - Prompt: `$` — `#5AAA6E`, 16px, JetBrains Mono
  - Command: `pdd generate auth_module` — `#E2E8F0`, 16px, JetBrains Mono
  - Status: Green checkmark `✓` — `#22C55E`, appears after typing completes
  - Label: "1. Generate its prompt" — `#94A3B8`, 14px, Inter, right-aligned
- **Step 2 (Y=220 inside terminal):**
  - Prompt: `$` — `#5AAA6E`
  - Command: `vim specs/auth_module.md  # add tests` — `#E2E8F0`
  - Comment portion: `# add tests` in `#64748B`
  - Status: Green checkmark `✓` — `#22C55E`
  - Label: "2. Add tests" — `#94A3B8`, 14px
- **Step 3 (Y=280 inside terminal):**
  - Prompt: `$` — `#5AAA6E`
  - Command: `pdd regenerate auth_module` — `#E2E8F0`
  - Status: Green checkmark `✓` — `#22C55E`
  - Label: "3. Regenerate" — `#94A3B8`, 14px
- **Step 4 (Y=340 inside terminal):**
  - Prompt: `$` — `#5AAA6E`
  - Command: `diff auth_module.py auth_module_regen.py` — `#E2E8F0`
  - Status: Green checkmark `✓` — `#22C55E`
  - Label: "4. Compare" — `#94A3B8`, 14px
- **Summary Line (Y=420 inside terminal):**
  - Text: `All tests passing ✓  Prompt is now source of truth.` — `#5AAA6E` at 0.8 opacity, 16px

### Animation Sequence
1. **Frame 0-30 (0-1s):** Terminal window fades in with scale (0.95→1.0). Title bar and dots appear. Cursor blinks at first prompt line
2. **Frame 30-90 (1-3s):** Step 1 types out character-by-character (~2 chars/frame). After typing completes, checkmark appears with a brief scale bounce (0→1.2→1.0). Label fades in
3. **Frame 90-150 (3-5s):** Step 2 types out. Comment text appears in dimmer color. Checkmark + label animate in
4. **Frame 150-210 (5-7s):** Step 3 types out. Checkmark + label animate in
5. **Frame 210-270 (7-9s):** Step 4 types out. Checkmark + label animate in
6. **Frame 270-320 (9-10.67s):** Brief pause, then summary line fades in. All four checkmarks pulse once together (brief glow)
7. **Frame 320-360 (10.67-12s):** Hold at final state

### Typography
- Terminal Title: JetBrains Mono, 13px, regular, `#64748B`
- Terminal Commands: JetBrains Mono, 16px, regular, `#E2E8F0`
- Terminal Prompt `$`: JetBrains Mono, 16px, regular, `#5AAA6E`
- Comments: JetBrains Mono, 16px, regular, `#64748B`
- Step Labels: Inter, 14px, regular (400), `#94A3B8`
- Summary Line: JetBrains Mono, 16px, regular, `#5AAA6E` at 0.8 opacity

### Easing
- Terminal fade/scale: `easeOut(cubic)`
- Character typing: `linear` (constant rate)
- Checkmark bounce: `spring({ damping: 12, stiffness: 200 })`
- Label fade: `easeOut(quad)`
- Summary fade: `easeOut(quad)`
- Checkmark pulse: `easeInOut(sine)`

## Narration Sync
> "Start with one module. Generate its prompt. Add tests. Regenerate. Compare."

Segment: `where_to_start_001` (2.96s – 8.60s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  {/* Terminal Window */}
  <Sequence from={0} durationInFrames={30}>
    <TerminalWindow width={900} height={500}>
      <TitleBar text="pdd-workflow" />
    </TerminalWindow>
  </Sequence>

  {/* Step 1: Generate */}
  <Sequence from={30} durationInFrames={60}>
    <TypewriterLine
      prompt="$"
      command="pdd generate auth_module"
      y={160}
    />
    <Sequence from={50}>
      <Checkmark color="#22C55E" />
      <StepLabel text="1. Generate its prompt" />
    </Sequence>
  </Sequence>

  {/* Step 2: Add Tests */}
  <Sequence from={90} durationInFrames={60}>
    <TypewriterLine
      prompt="$"
      command='vim specs/auth_module.md  # add tests'
      commentStart={27}
      y={220}
    />
    <Sequence from={50}>
      <Checkmark color="#22C55E" />
      <StepLabel text="2. Add tests" />
    </Sequence>
  </Sequence>

  {/* Step 3: Regenerate */}
  <Sequence from={150} durationInFrames={60}>
    <TypewriterLine
      prompt="$"
      command="pdd regenerate auth_module"
      y={280}
    />
    <Sequence from={50}>
      <Checkmark color="#22C55E" />
      <StepLabel text="3. Regenerate" />
    </Sequence>
  </Sequence>

  {/* Step 4: Compare */}
  <Sequence from={210} durationInFrames={60}>
    <TypewriterLine
      prompt="$"
      command="diff auth_module.py auth_module_regen.py"
      y={340}
    />
    <Sequence from={50}>
      <Checkmark color="#22C55E" />
      <StepLabel text="4. Compare" />
    </Sequence>
  </Sequence>

  {/* Summary */}
  <Sequence from={270} durationInFrames={50}>
    <SummaryLine
      text="All tests passing ✓  Prompt is now source of truth."
      color="#5AAA6E"
      y={420}
    />
    <CheckmarkGroupPulse />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0A1628",
  "terminal": {
    "width": 900,
    "height": 500,
    "background": "#111827",
    "titleBar": "#1E293B",
    "borderRadius": 12
  },
  "steps": [
    {
      "step": 1,
      "command": "pdd generate auth_module",
      "label": "1. Generate its prompt",
      "y": 160
    },
    {
      "step": 2,
      "command": "vim specs/auth_module.md  # add tests",
      "label": "2. Add tests",
      "y": 220
    },
    {
      "step": 3,
      "command": "pdd regenerate auth_module",
      "label": "3. Regenerate",
      "y": 280
    },
    {
      "step": 4,
      "command": "diff auth_module.py auth_module_regen.py",
      "label": "4. Compare",
      "y": 340
    }
  ],
  "summary": {
    "text": "All tests passing ✓  Prompt is now source of truth.",
    "color": "#5AAA6E",
    "y": 420
  }
}
```

---
