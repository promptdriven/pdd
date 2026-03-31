[Remotion]

# Section 0.8: Code Regeneration — Delete and Rebuild

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:26 - 0:31

## Visual Description

The dramatic pivot of the cold open. The entire patched `validate_email()` function from spec 07 SELECTS (blue highlight sweeps down all 30 lines) and then DELETES in a single keystroke. The editor is empty for a brief, dramatic beat — just a blank file with a blinking cursor.

Then the function REGENERATES. Clean, formatted code flows in from the top — line by line, rapid but readable. No patch comments. No workarounds. No accumulated cruft. The code is fresh, complete, and correct. In the bottom-right corner, a subtle terminal overlay shows `pdd generate email_validator` completing with a green checkmark.

The contrast is visceral: 30 lines of patched mess → empty → 30 lines of clean code. All in under 2 seconds of animation.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#1E1E2E` (VS Code dark theme)
- Line numbers visible on left gutter: `#4A5568` at 0.4

### Chart/Visual Elements

#### Selection Highlight
- Full-block selection: `#264F78` at 0.4 (VS Code selection blue)
- Sweeps from line 1 to line 30

#### Deletion Effect
- Lines collapse upward rapidly
- Brief empty state: just cursor on line 1

#### Regenerated Code
- Same `validate_email()` function but clean — no patch comments
- Font: JetBrains Mono, 16px, `#E2E8F0`
- Keywords: `#C792EA` (purple)
- Strings: `#C3E88D` (green)
- Comments: only clean docstring, `#546E7A`

#### Terminal Overlay (bottom-right corner)
- Semi-transparent black background: `#000000` at 0.85
- Rounded corners: 8px
- Size: 400x60px, positioned at bottom-right with 20px margin
- Text: `$ pdd generate email_validator` → `✓ Generated (0.8s)`
- Font: JetBrains Mono, 13px, `#4ADE80` (green)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Selection highlight sweeps down all lines of the patched function.
2. **Frame 15-25 (0.5-0.83s):** All selected code deletes. Lines collapse. Empty editor.
3. **Frame 25-35 (0.83-1.17s):** Brief hold on empty editor. Cursor blinks once.
4. **Frame 35-90 (1.17-3s):** Clean code regenerates — flows in line by line from the top. No patch comments. Clean structure.
5. **Frame 70-100 (2.33-3.33s):** Terminal overlay fades in at bottom-right. Shows `pdd generate email_validator` completing.
6. **Frame 100-150 (3.33-5s):** Hold on clean code + terminal. Green checkmark appears on terminal.

### Typography
- Code: JetBrains Mono, 16px, regular (400)
- Terminal command: JetBrains Mono, 13px, `#94A3B8`
- Terminal success: JetBrains Mono, 13px, bold, `#4ADE80`
- Line numbers: JetBrains Mono, 14px, `#4A5568` at 0.4

### Easing
- Selection sweep: linear, 0.5 frames per line
- Deletion collapse: `easeIn(quad)` over 10 frames
- Regeneration flow: linear, 1.5 frames per line
- Terminal fade-in: `easeOut(quad)` over 15 frames
- Checkmark pop: `easeOut(back)` over 10 frames

## Narration Sync
> "watch this. It deletes. Regenerates."
> "15 lines of prompt, 200 lines of clean code."

Segments: `cold_open_007`, `cold_open_008`

- **26.32s** (seg 007): Selection sweep — "watch this"
- **27.00s**: Deletion — "It deletes"
- **27.56s** (seg 007 ends / seg 008 begins): Regeneration begins — "Regenerates"
- **28.50s**: Clean code flowing in — "15 lines of prompt"
- **32.68s** (seg 008 ends): Terminal visible, generation complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#1E1E2E' }}>
    <LineNumbers start={1} count={30} font="JetBrains Mono"
      size={14} color="#4A5568" opacity={0.4} />

    {/* Selection sweep over patched code */}
    <Sequence from={0} durationInFrames={15}>
      <SelectionSweep lines={30} color="#264F78" opacity={0.4}
        direction="down" duration={15} />
      <CodeBlock code={patchedCode} font="JetBrains Mono" size={16} />
    </Sequence>

    {/* Deletion */}
    <Sequence from={15} durationInFrames={10}>
      <CollapseDelete lines={30} duration={10} easing="easeInQuad" />
    </Sequence>

    {/* Empty beat */}
    <Sequence from={25} durationInFrames={10}>
      <BlinkingCursor x={80} y={24} width={2} height={20}
        color="#E2E8F0" onFrames={15} offFrames={15} />
    </Sequence>

    {/* Regeneration */}
    <Sequence from={35}>
      <TypewriterCode
        code={cleanCode}
        font="JetBrains Mono" size={16}
        lineDelay={1.5}
      />
    </Sequence>

    {/* Terminal overlay */}
    <Sequence from={70}>
      <FadeIn duration={15}>
        <TerminalOverlay
          command="pdd generate email_validator"
          result="✓ Generated (0.8s)"
          position={{ x: 1500, y: 1000 }}
          resultColor="#4ADE80"
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
  "editorTheme": "dark",
  "language": "python",
  "functionName": "validate_email",
  "phases": [
    { "phase": "select", "frames": [0, 15], "description": "Selection sweep over patched code" },
    { "phase": "delete", "frames": [15, 25], "description": "All code deletes" },
    { "phase": "empty", "frames": [25, 35], "description": "Brief empty editor beat" },
    { "phase": "regenerate", "frames": [35, 90], "description": "Clean code flows in" },
    { "phase": "terminal", "frames": [70, 150], "description": "pdd generate overlay" }
  ],
  "terminalCommand": "pdd generate email_validator",
  "narrationSegments": ["cold_open_007", "cold_open_008"]
}
```

---
