[Remotion]

# Section 0.8: Prompt File and Code Generation

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:33 - 0:37

## Visual Description

Clean terminal on a dark background. A file appears: `email_validator.prompt` — rendered as a clean document with about 15 lines of natural language. The prompt file is readable, clear, human-authored: it describes validation rules in plain English ("Validate email format using RFC 5322", "Support international domain names", "Return detailed error messages"). The viewer should be able to read enough to understand this is a specification, not code.

Then the terminal runs `pdd generate email_validator`. Code flows out beneath — roughly 200 lines of clean Python, streaming line by line. The output is fast, formatted, complete. The visual contrast is stark: 15 lines of human intent → 200 lines of working code.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy)
- Grid lines: None

### Chart/Visual Elements

#### Prompt File Display
- Position: Left side of screen, x: 100-860, y: 80-600
- File label: `email_validator.prompt` in `#94A3B8`, JetBrains Mono 13px
- File icon: Document icon in `#89B4FA`
- Content area: `#11111B` background, 8px border-radius, 1px border `#2D2D3D`
- Content: 15 lines of natural language in `#CDD6F4`, JetBrains Mono 13px
- Key lines highlighted: `#A6E3A1` for rule definitions

#### Terminal / Output Area
- Position: Right side of screen, x: 900-1820, y: 80-1000
- Background: `#11111B`, 8px border-radius
- Command line: `$ pdd generate email_validator` in `#94A3B8`
- Output: Python code streaming, syntax-highlighted
- Line counter: Subtle count in bottom-right corner, `#6C7086`

#### Arrow / Flow Indicator
- Position: Center, between prompt file and output
- Arrow: `→` in `#89B4FA`, 36px, with subtle pulse
- Label below: "generate" in `#6C7086`, 12px

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Prompt file fades in on the left. Clean document, 15 lines visible.
2. **Frame 20-40 (0.67-1.33s):** Arrow appears center. Terminal area appears on right.
3. **Frame 40-50 (1.33-1.67s):** Command types in: `$ pdd generate email_validator`
4. **Frame 50-130 (1.67-4.33s):** Code streams out in the terminal — 200 lines flowing rapidly. Line counter ticks up. Syntax highlighting applies in real-time.
5. **Frame 130-150 (4.33-5s):** Streaming completes. Line counter shows `200 lines`. Green checkmark appears after command.

### Typography
- File label: JetBrains Mono, 13px, `#94A3B8`
- Prompt content: JetBrains Mono, 13px, `#CDD6F4`
- Command: JetBrains Mono, 14px, `#94A3B8`
- Code output: JetBrains Mono, 11px, syntax colors
- Line counter: JetBrains Mono, 11px, `#6C7086`
- Arrow: Inter, 36px, `#89B4FA`

### Easing
- Prompt file fade-in: `easeOut(quad)` over 20 frames
- Arrow appear: `easeOut(cubic)` over 10 frames
- Terminal appear: `easeOut(quad)` over 10 frames
- Command type-in: `linear`, 2 frames per character
- Code stream: `linear`, rapid scroll
- Checkmark: `easeOut(back)` over 10 frames (slight overshoot)

## Narration Sync
> "15 lines of prompt, and the code regenerates. 200 lines, clean, tested."

Segment: `cold_open_008` (latter portion)

- **32.88s**: Prompt file appears — "15 lines of prompt"
- **34.0s**: Arrow and terminal appear
- **34.5s**: `pdd generate` command runs
- **36.0s**: Code streaming — "200 lines, clean, tested"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  {/* Background */}
  <Background color="#0A0F1A" />

  {/* Prompt file - left side */}
  <Sequence from={0} durationInFrames={150}>
    <FadeIn durationFrames={20}>
      <PromptFileDisplay
        filename="email_validator.prompt"
        lines={PROMPT_LINES}
        position={{ x: 100, y: 80, width: 760, height: 520 }}
      />
    </FadeIn>
  </Sequence>

  {/* Arrow indicator */}
  <Sequence from={20} durationInFrames={130}>
    <FadeIn durationFrames={10}>
      <FlowArrow
        position={{ x: 880, y: 340 }}
        color="#89B4FA"
        label="generate"
      />
    </FadeIn>
  </Sequence>

  {/* Terminal output - right side */}
  <Sequence from={30} durationInFrames={120}>
    <FadeIn durationFrames={10}>
      <TerminalPanel position={{ x: 900, y: 80, width: 920, height: 920 }}>
        <Sequence from={10} durationInFrames={110}>
          <TypewriterCommand
            command="pdd generate email_validator"
            framesPerChar={2}
          />
        </Sequence>
        <Sequence from={20} durationInFrames={100}>
          <CodeStream
            code={EMAIL_VALIDATOR_CODE}
            language="python"
            totalLines={200}
            streamDuration={80}
          />
        </Sequence>
        <Sequence from={100} durationInFrames={20}>
          <LineCounter count={200} color="#6C7086" />
          <Checkmark color="#A6E3A1" easing="easeOutBack" />
        </Sequence>
      </TerminalPanel>
    </FadeIn>
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "remotion_animation",
  "componentId": "prompt_file_generate",
  "durationFrames": 150,
  "fps": 30,
  "narrationSegments": ["cold_open_008"],
  "promptFile": "email_validator.prompt",
  "promptLines": 15,
  "outputLines": 200,
  "pddCommand": "pdd generate email_validator"
}
```

---
