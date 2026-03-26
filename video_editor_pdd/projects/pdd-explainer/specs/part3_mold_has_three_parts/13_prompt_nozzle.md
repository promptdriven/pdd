[Remotion]

# Section 3.13: Prompt Nozzle — Specification Flows In

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 2:56 - 3:14

## Visual Description

The mold cross-section returns, now focused on the nozzle region. The nozzle (teal) highlights and labels appear: "intent", "requirements", "constraints" — the three things a prompt encodes. These labels orbit the nozzle briefly, then settle into position.

Then natural-language text flows from the nozzle into the mold like injection material. The text is readable: "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode." The text is styled as a warm teal color, flowing like liquid from the nozzle into the cavity. A file label briefly appears: `user_parser.prompt`.

In the terminal corner: `pdd generate user_parser.prompt` runs twice. Each run produces slightly different code — different variable names, different structure — but both pass all tests. The point: the prompt defines WHAT, not HOW.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Mold (nozzle emphasized)
- Same cross-section, nozzle region highlighted at full opacity
- Nozzle: `#2DD4BF` fill at 0.2, stroke at 0.7
- Other regions: dimmed to 0.15

#### Nozzle Labels
- "intent" — Inter, 14px, bold, `#2DD4BF` at 0.8, orbiting then settling at left
- "requirements" — Inter, 14px, bold, `#2DD4BF` at 0.8, settling at right
- "constraints" — Inter, 14px, bold, `#2DD4BF` at 0.8, settling below

#### Flowing Text
- "Parse user IDs from untrusted input." — Inter, 13px, `#2DD4BF` at 0.6
- "Return None on failure, never throw." — Inter, 13px, `#2DD4BF` at 0.6
- "Handle unicode." — Inter, 13px, `#2DD4BF` at 0.6
- Text flows downward from nozzle into cavity, following the injection path
- Trail effect: text leaves a subtle gradient trail

#### File Label
- `user_parser.prompt` — JetBrains Mono, 12px, `#2DD4BF` at 0.4
- Small file icon, positioned near nozzle

#### Dual Generation Terminal
- Position: bottom-right, 500×250px
- Run 1: `$ pdd generate user_parser.prompt` → code snippet A
- Run 2: `$ pdd generate user_parser.prompt` → code snippet B (different)
- Both show `✓ All tests passing`
- Code A and B are visually different but both valid

### Animation Sequence
1. **Frame 0-60 (0-2s):** Mold returns, nozzle region brightens. Other regions dim.
2. **Frame 60-150 (2-5s):** Labels "intent", "requirements", "constraints" orbit nozzle then settle.
3. **Frame 150-270 (5-9s):** Text flows from nozzle into cavity. Each line appears and flows downward.
4. **Frame 270-330 (9-11s):** File label `user_parser.prompt` appears near nozzle.
5. **Frame 330-450 (11-15s):** Terminal shows first generation. Code snippet A appears.
6. **Frame 450-540 (15-18s):** Terminal shows second generation. Code snippet B appears (different). Both pass. Label: "Same prompt. Different code. Same behavior."

### Typography
- Nozzle labels: Inter, 14px, bold (700), `#2DD4BF` at 0.8
- Flowing text: Inter, 13px, `#2DD4BF` at 0.6
- File label: JetBrains Mono, 12px, `#2DD4BF` at 0.4
- Terminal: JetBrains Mono, 11px, `#E2E8F0` / `#4ADE80`
- Bottom label: Inter, 14px, `#94A3B8` at 0.5

### Easing
- Nozzle brighten: `easeOut(cubic)` over 30 frames
- Label orbit: `easeOut(cubic)` over 40 frames (orbital motion + deceleration)
- Text flow: `easeInOut(sine)` — organic downward flow
- File label: `easeOut(quad)` over 15 frames
- Terminal type: stagger 2 frames per character

## Narration Sync
> "Second: the prompt. Your specification of what you want."
> "The prompt doesn't define the walls — tests do that. The prompt defines what you're asking for and why."
> "Notice something subtle: the exact implementation can vary. What's locked is the behavior. The code is flexible; the contract is fixed."

Segments: `part3_mold_has_three_parts_018`, `part3_mold_has_three_parts_019`, `part3_mold_has_three_parts_020`

- **2:56** ("Second: the prompt"): Nozzle highlights, labels appear
- **3:02** ("prompt doesn't define the walls"): Text flows into cavity
- **3:08** ("exact implementation can vary"): Dual generation shown

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.05} />
    <MoldOutline cx={960} cy={400} emphasize="nozzle" dimOthers={0.15} />

    {/* Nozzle labels */}
    <Sequence from={60}>
      <OrbitAndSettle labels={["intent", "requirements", "constraints"]}
        cx={960} cy={280} orbitRadius={80}
        font="Inter" fontSize={14} weight={700}
        color="#2DD4BF" opacity={0.8}
        orbitDuration={40} settleDuration={20} />
    </Sequence>

    {/* Flowing text */}
    <Sequence from={150}>
      <FlowingText
        lines={[
          "Parse user IDs from untrusted input.",
          "Return None on failure, never throw.",
          "Handle unicode."
        ]}
        startY={320} endY={550}
        font="Inter" fontSize={13} color="#2DD4BF" opacity={0.6}
        stagger={30} flowDuration={40} />
    </Sequence>

    {/* File label */}
    <Sequence from={270}>
      <FadeIn duration={15}>
        <FileLabel text="user_parser.prompt"
          font="JetBrains Mono" fontSize={12}
          color="#2DD4BF" opacity={0.4}
          x={1100} y={260} />
      </FadeIn>
    </Sequence>

    {/* Dual generation terminal */}
    <Sequence from={330}>
      <DualTerminal x={1200} y={700} width={500} height={250}>
        <Generation label="Run 1" command="pdd generate user_parser.prompt"
          code={CODE_A} result="✓ All tests passing" />
        <Sequence from={120}>
          <Generation label="Run 2" command="pdd generate user_parser.prompt"
            code={CODE_B} result="✓ All tests passing" />
        </Sequence>
      </DualTerminal>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "prompt_nozzle",
  "nozzleLabels": ["intent", "requirements", "constraints"],
  "promptText": [
    "Parse user IDs from untrusted input.",
    "Return None on failure, never throw.",
    "Handle unicode."
  ],
  "promptFile": "user_parser.prompt",
  "dualGeneration": true,
  "nozzleColor": "#2DD4BF",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_018", "part3_mold_has_three_parts_019", "part3_mold_has_three_parts_020"]
}
```

---
