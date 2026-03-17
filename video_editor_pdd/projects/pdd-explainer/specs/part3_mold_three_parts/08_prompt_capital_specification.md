[Remotion]

# Section 3.8: Prompt Capital — The Specification That Governs

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 15:30 - 15:50

## Visual Description

This spec covers the second type of capital: the prompt as specification. It has three visual beats.

**Beat 1 — Nozzle Labels (frames 0-150):** Returning to the mold diagram from earlier, the injection nozzle region illuminates blue. Labels flow into the nozzle like text being injected: "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode." A file label appears: `user_parser.prompt`. The nozzle is the entry point — the specification of what you want.

**Beat 2 — Two Generations, Same Spec (frames 150-360):** A split view shows the same prompt generating code twice. Two code panels appear side by side. The code is visibly different — different variable names, different structure — but both have green checkmarks. The behavior is locked; the implementation is flexible. A label below reads: "What's locked is the behavior. The code is flexible; the contract is fixed."

**Beat 3 — Compression Ratio (frames 360-600):** The prompt panel glows on the left — small, maybe 10-15 lines of clean natural language. To its right, the generated code file is 10× taller, scrolling. A ratio badge appears: "1:5 to 1:10". Then a split comparison of two context windows: LEFT filled with 15,000 tokens of dense code (overwhelming), RIGHT filled with prompts for ten modules (clean, readable). Both windows are the same pixel size but the right represents 10× more system knowledge. Label: "5-10× context window advantage."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: engineering grid, 40px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Beat 1 — Nozzle Labels

**Mold Diagram (carried forward, centered at 960, 500)**
- All regions dimmed to 0.15 except nozzle
- Nozzle: `#4A90D9` at 0.6, 3px stroke, 12px glow at 0.2

**Flowing Text**
- Text particles flowing into nozzle from above, like liquid text injection
- Content: "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode."
- Font: JetBrains Mono, 11px, `#4A90D9` at 0.7
- Flow speed: 2px/frame downward, slight horizontal wobble
- File label: `user_parser.prompt` — JetBrains Mono, 10px, `#64748B` at 0.5, at top of nozzle

#### Beat 2 — Two Code Panels

**Left Panel: Generation A (x: 160, y: 200, 340w × 500h)**
- Background: `#1E293B` at 0.6, 1px `#334155` border, rounded 6px
- Title bar: `user_parser_v1.py` — JetBrains Mono, 10px
- Code: syntax-highlighted Python, using `class UserParser` style
- Green checkmark overlay: `#5AAA6E` at 0.6, 40px, bottom-right corner

**Right Panel: Generation B (x: 540, y: 200, 340w × 500h)**
- Same format, different code: using `def parse_user_id()` functional style
- Different variable names, different structure
- Same green checkmark: passes all tests

**Center Label**
- "≠ code" — Inter, 20px, `#64748B` at 0.4, between panels at y: 450
- "= behavior" — Inter, 20px, `#5AAA6E` at 0.6, below

**Caption (y: 750)**
- "What's locked is the *behavior*. The code is flexible; the contract is fixed." — Inter, 14px, `#E2E8F0` at 0.7
- "behavior" and "contract" in bold

#### Beat 3 — Compression Ratio

**Prompt Panel (left, x: 100, y: 180, 300w × 300h)**
- Clean natural language, 12 lines
- Soft blue glow: `#4A90D9` at 0.1
- Ratio badge: "1:5 to 1:10" — Inter, 24px, bold (700), `#4A90D9`, in a pill `#4A90D9` at 0.1, positioned at (250, 530)

**Code Panel (right, x: 450, y: 80, 300w × 600h)**
- Dense code, 200+ lines scrolling
- Dimmer: `#94A3B8` at 0.3
- Scroll speed: 0.5px/frame upward, continuous
- Height comparison arrow between panels: labeled "10×"

**Context Window Comparison (right half, x: 900)**
- LEFT window (x: 900, y: 200, 400w × 600h): `#1E293B` background
  - Filled with dense code text, `#94A3B8` at 0.15, representing 15,000 tokens
  - Label above: "15,000 tokens of code" — Inter, 11px, `#64748B`
  - Visual: cramped, overwhelming, hard to parse
- RIGHT window (x: 1350, y: 200, 400w × 600h): `#1E293B` background
  - Filled with 10 clean prompt blocks, `#4A90D9` at 0.15, with clear spacing
  - Label above: "Prompts for 10 modules" — Inter, 11px, `#4A90D9`
  - Visual: spacious, readable, organized
- Label below both: "Same context window. 10× more system knowledge." — Inter, 14px, `#E2E8F0` at 0.7

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold diagram fades in, dimmed. Nozzle illuminates blue.
2. **Frame 30-90 (1-3s):** Text particles flow into nozzle. Prompt content visible as flowing text. `user_parser.prompt` label appears.
3. **Frame 90-150 (3-5s):** Text settles into nozzle. Nozzle pulses. Labels "intent", "requirements", "constraints" reappear briefly.

4. **Frame 150-180 (5-6s):** Mold diagram fades out. Two code panels appear side by side.
5. **Frame 180-270 (6-9s):** Code types in both panels simultaneously — different code, same prompt. Syntax highlighting active.
6. **Frame 270-330 (9-11s):** Green checkmarks appear on both panels (spring animation). "≠ code" and "= behavior" labels appear. Caption fades in.
7. **Frame 330-360 (11-12s):** Hold on the two-generation comparison.

8. **Frame 360-390 (12-13s):** Panels dissolve. Prompt panel and code panel appear for compression ratio.
9. **Frame 390-450 (13-15s):** Code panel scrolls, showing its 200+ line length. Height arrow draws. Ratio badge appears: "1:5 to 1:10".
10. **Frame 450-510 (15-17s):** Context window comparison slides in from right. LEFT fills with dense code (overwhelming). RIGHT fills with clean prompts (spacious).
11. **Frame 510-540 (17-18s):** "Same context window. 10× more system knowledge." caption appears.
12. **Frame 540-600 (18-20s):** Hold on context window contrast. Right window pulses blue gently.

### Typography
- Flowing text: JetBrains Mono, 11px, `#4A90D9` at 0.7
- File labels: JetBrains Mono, 10px, `#64748B` at 0.5
- Code: JetBrains Mono, 10px, syntax-highlighted
- Comparison labels: Inter, 20px, `#64748B` / `#5AAA6E`
- Captions: Inter, 14px, `#E2E8F0` at 0.7
- Ratio badge: Inter, 24px, bold (700), `#4A90D9`
- Context labels: Inter, 11px, `#64748B` / `#4A90D9`

### Easing
- Nozzle illuminate: `easeOut(quad)` over 20 frames
- Text flow: `linear` vertical, `easeInOut(sine)` horizontal wobble
- Code typing: `linear`, 2 frames/char
- Checkmark appear: `spring({ stiffness: 200, damping: 10 })` scale from 0
- Ratio badge: `spring({ stiffness: 150, damping: 12 })` scale from 0.8
- Context window slide: `easeOut(cubic)` from x+40, 25 frames
- Blue pulse: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "Second: the prompt. Your specification of what you want."
> "The prompt doesn't define the walls — tests do that. The prompt defines what you're asking for and why."
> "Notice something subtle: the exact implementation can vary. What's locked is the behavior. The code is flexible; the contract is fixed."
> "A good prompt is a fifth to a tenth the size of the code it generates. Think of the prompt as your header file."
> "You're giving it natural language — its strongest modality — in a window that's five to ten times more spacious."

Segment: `part3_008`

- **15:30** ("Second: the prompt"): Nozzle illuminates, text flows in
- **15:34** ("The prompt defines what you're asking for"): Labels appear
- **15:37** ("the exact implementation can vary"): Two code panels, different code
- **15:40** ("the behavior... the contract is fixed"): Green checkmarks, caption
- **15:43** ("A good prompt is a fifth to a tenth"): Compression ratio view
- **15:47** ("five to ten times more spacious"): Context window comparison

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <EngineeringGrid spacing={40} color="#1E293B" opacity={0.03} />

    {/* Beat 1: Nozzle Labels */}
    <Sequence from={0} durationInFrames={150}>
      <MoldCrossSection opacity={0.15} nozzleHighlight={{
        color: '#4A90D9', opacity: 0.6, glow: { blur: 12, opacity: 0.2 }
      }} />
      <Sequence from={30}>
        <TextFlow
          text="Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode."
          entryPoint={[960, 100]} target={[960, 280]}
          font="JetBrains Mono" size={11}
          color="#4A90D9" opacity={0.7}
          flowSpeed={2} wobble />
        <FileLabel text="user_parser.prompt" position={[960, 160]}
          font="JetBrains Mono" size={10}
          color="#64748B" opacity={0.5} />
      </Sequence>
    </Sequence>

    {/* Beat 2: Two Generations */}
    <Sequence from={150} durationInFrames={210}>
      <CodePanel x={160} y={200} width={340} height={500}
        filename="user_parser_v1.py"
        code={classStyleCode} typeSpeed={2}
        checkmark={{ at: 120, color: '#5AAA6E' }} />
      <CodePanel x={540} y={200} width={340} height={500}
        filename="user_parser_v2.py"
        code={functionalStyleCode} typeSpeed={2}
        checkmark={{ at: 120, color: '#5AAA6E' }} />

      <Sequence from={120}>
        <FadeIn duration={15}>
          <Text text="≠ code" font="Inter" size={20}
            color="#64748B" opacity={0.4}
            x={510} y={430} align="center" />
          <Text text="= behavior" font="Inter" size={20}
            color="#5AAA6E" opacity={0.6}
            x={510} y={470} align="center" />
        </FadeIn>
      </Sequence>

      <Sequence from={140}>
        <FadeIn duration={20}>
          <RichText x={440} y={750} font="Inter" size={14}
            color="#E2E8F0" opacity={0.7}>
            What's locked is the <Bold>behavior</Bold>.
            The code is flexible; the <Bold>contract</Bold> is fixed.
          </RichText>
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Beat 3: Compression Ratio */}
    <Sequence from={360} durationInFrames={240}>
      <PromptPanel x={100} y={180} width={300} height={300}
        content={promptContent} glow="#4A90D9" glowOpacity={0.1} />
      <CodeScrollPanel x={450} y={80} width={300} height={600}
        lineCount={200} scrollSpeed={0.5} opacity={0.3} />
      <HeightArrow from={[420, 180]} to={[420, 480]}
        label="10×" color="#4A90D9" />

      <Sequence from={30}>
        <SpringScale stiffness={150} damping={12} from={0.8}>
          <Pill text="1:5 to 1:10" color="#4A90D9"
            bgOpacity={0.1} font="Inter" size={24} weight={700}
            x={250} y={530} />
        </SpringScale>
      </Sequence>

      <Sequence from={90}>
        <ContextWindowComparison
          leftWindow={{
            x: 900, y: 200, width: 400, height: 600,
            label: '15,000 tokens of code',
            fill: { color: '#94A3B8', opacity: 0.15, style: 'dense' }
          }}
          rightWindow={{
            x: 1350, y: 200, width: 400, height: 600,
            label: 'Prompts for 10 modules',
            fill: { color: '#4A90D9', opacity: 0.15, style: 'clean_blocks' }
          }}
          caption="Same context window. 10× more system knowledge."
        />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "multi_beat",
  "beats": [
    {
      "id": "nozzle_labels",
      "type": "mold_region_focus",
      "region": "nozzle",
      "color": "#4A90D9",
      "promptContent": "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.",
      "file": "user_parser.prompt"
    },
    {
      "id": "two_generations",
      "type": "code_comparison",
      "variants": ["class UserParser (OOP)", "def parse_user_id (functional)"],
      "sharedResult": "All tests pass",
      "caption": "What's locked is the behavior. The code is flexible; the contract is fixed."
    },
    {
      "id": "compression_ratio",
      "type": "size_comparison",
      "ratio": "1:5 to 1:10",
      "promptLines": 12,
      "codeLines": 200,
      "contextAdvantage": "5-10×",
      "leftWindow": { "tokens": 15000, "content": "raw code" },
      "rightWindow": { "tokens": 15000, "content": "10 module prompts" }
    }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_008"]
}
```

---
