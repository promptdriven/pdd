[Remotion]

# Section 3.10: Three Components Table — The Complete Specification

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 17:30 - 17:46

## Visual Description

The culminating visual for Part 3. A clean, authoritative summary table materializes in the center of the screen, showing all three components of the PDD mold working together.

First, the full mold diagram appears one final time — all three regions glowing in their respective colors (amber walls, blue nozzle, green cavity). Prompt text flows in through the nozzle, passes through the green grounding material, fills the mold cavity, and is constrained by the amber test walls. Clean, generated code emerges at the bottom — the output.

Then the mold diagram slides left and shrinks, making room for the summary table on the right:

| Component | Encodes | Owner |
|-----------|---------|-------|
| Prompt | WHAT (intent) | Developer |
| Grounding | HOW (style) | Automatic |
| Tests | CORRECTNESS | Accumulated |

Each row appears with the corresponding color: blue for Prompt, green for Grounding, amber for Tests. Below the table, a single line pulses with emphasis: **"When these conflict, tests win. Always."** The Tests row glows brighter, asserting dominance.

The final beat: the generated code that emerged from the mold glows briefly — then the glow fades. The code is just output. The mold (prompt + grounding + tests) continues to glow. "The code is output. The mold is what matters."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: engineering grid, 40px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Mold Diagram (left side after transition, centered at 350, 500, scaled 0.5×)
- All three regions glowing: walls `#D9944A`, nozzle `#4A90D9`, cavity `#5AAA6E`
- Animated flow: prompt text → grounding → constrained by walls → code output
- Scale transition: 1.0× → 0.5× as it slides left

#### Flow Animation
- Input: natural language text particles entering nozzle, `#4A90D9` at 0.6
- Through grounding: particles pick up green tint, `#5AAA6E` at 0.3
- Constrained by walls: particles redirect at wall boundaries, amber flash
- Output: code text emerges at bottom, `#E2E8F0` at 0.6

#### Summary Table (right side, x: 650-1750, y: 250-650)
- Table background: `#1E293B` at 0.4, rounded 12px
- Header row: `#0F172A`, Inter, 12px, semi-bold (600), `#94A3B8`, letter-spacing 2px
  - "COMPONENT" | "ENCODES" | "OWNER"
- Column widths: 300 | 350 | 250
- Row height: 80px
- Horizontal dividers: 1px, `#334155` at 0.2

**Row 1 — Prompt (blue)**
- Left: blue dot `#4A90D9` + "Prompt" — Inter, 18px, semi-bold (600), `#4A90D9`
- Center: "WHAT (intent)" — Inter, 16px, `#E2E8F0` at 0.8
- Right: "Developer" — Inter, 14px, `#94A3B8` at 0.6
- Row left border accent: 3px, `#4A90D9` at 0.5

**Row 2 — Grounding (green)**
- Left: green dot `#5AAA6E` + "Grounding" — Inter, 18px, semi-bold (600), `#5AAA6E`
- Center: "HOW (style)" — Inter, 16px, `#E2E8F0` at 0.8
- Right: "Automatic" — Inter, 14px, `#94A3B8` at 0.6
- Row left border accent: 3px, `#5AAA6E` at 0.5

**Row 3 — Tests (amber, emphasized)**
- Left: amber dot `#D9944A` + "Tests" — Inter, 18px, bold (700), `#D9944A`
- Center: "CORRECTNESS" — Inter, 16px, bold (700), `#E2E8F0`
- Right: "Accumulated" — Inter, 14px, `#94A3B8` at 0.6
- Row left border accent: 4px, `#D9944A` at 0.7
- Row background: `#D9944A` at 0.04 (subtle amber wash)

#### Conflict Resolution Line (below table, y: 700)
- "When these conflict, tests win. Always." — Inter, 18px, `#E2E8F0` at 0.8
- "tests win" in bold, `#D9944A`
- "Always." in bold, `#D9944A`
- Subtle underline: 2px, `#D9944A` at 0.3, drawing under "tests win. Always."
- Pulsing glow on the Tests row synced with this text

#### Final Beat — Code Output (bottom center, y: 850)
- Code snippet: small, clean, `#E2E8F0` at 0.6, JetBrains Mono, 10px
- Glow: `#E2E8F0` at 0.15 → fades to 0
- After glow fades, code dims to 0.2
- Mold components (table rows) remain glowing
- Caption: "The code is output. The mold is what matters." — Inter, 14px, `#D9944A` at 0.7

### Animation Sequence
1. **Frame 0-60 (0-2s):** Full mold diagram visible, all three regions glowing. Flow animation runs: text → grounding → walls → code.
2. **Frame 60-120 (2-4s):** Mold diagram slides left and scales to 0.5×. Table background fades in on the right.
3. **Frame 120-180 (4-6s):** Table header row types in. First divider draws.
4. **Frame 180-220 (6-7.33s):** Row 1 (Prompt) slides in from right. Blue dot appears. Text fills cells.
5. **Frame 220-260 (7.33-8.67s):** Row 2 (Grounding) slides in. Green dot. Text fills.
6. **Frame 260-310 (8.67-10.33s):** Row 3 (Tests) slides in with extra emphasis — slightly slower, amber background wash appears, border thicker. Text fills in bold.
7. **Frame 310-370 (10.33-12.33s):** Conflict resolution line appears below table. "tests win" and "Always." glow amber. Underline draws. Tests row pulses.
8. **Frame 370-420 (12.33-14s):** Code output appears below mold diagram. It glows briefly — `#E2E8F0` at 0.15.
9. **Frame 420-450 (14-15s):** Code glow fades to 0. Code dims to 0.2. Table rows remain bright. The mold matters, not the code.
10. **Frame 450-480 (15-16s):** Caption appears: "The code is output. The mold is what matters." Hold.

### Typography
- Table header: Inter, 12px, semi-bold (600), `#94A3B8`, letter-spacing 2px
- Component names: Inter, 18px, semi-bold/bold, respective colors
- Encodes values: Inter, 16px, `#E2E8F0` at 0.8
- Owner values: Inter, 14px, `#94A3B8` at 0.6
- Conflict line: Inter, 18px, `#E2E8F0` at 0.8, bold on key phrases `#D9944A`
- Final caption: Inter, 14px, `#D9944A` at 0.7
- Code output: JetBrains Mono, 10px, `#E2E8F0` at 0.6 → 0.2

### Easing
- Mold slide + scale: `easeInOut(cubic)` over 40 frames
- Table background: `easeOut(quad)` over 20 frames
- Row slide-in: `easeOut(cubic)` from x+30, 20 frames each
- Tests row: `easeOut(cubic)` from x+30, 25 frames (slower for emphasis)
- Conflict line: `easeOut(quad)` over 20 frames
- Underline draw: `easeInOut(quad)` over 15 frames
- Tests row pulse: `easeInOut(sine)` on 30-frame cycle, border opacity 0.5 → 0.9
- Code glow fade: `easeIn(quad)` over 30 frames
- Code dim: `easeOut(quad)` over 20 frames to 0.2

## Narration Sync
> "Prompt plus tests plus grounding. Intent plus constraints plus style. Together, they form a complete specification."
> "When these conflict, tests win. Always. The walls override the specification. The specification overrides the style."
> "The code is output. The mold is what matters."

Segment: `part3_010`

- **17:30** ("Prompt plus tests plus grounding"): Mold diagram with flow, table begins
- **17:34** ("Together, they form a complete specification"): Table rows populate
- **17:38** ("When these conflict, tests win"): Conflict line, Tests row pulses
- **17:41** ("The walls override the specification"): Hierarchy emphasis
- **17:44** ("The code is output"): Code glows then fades
- **17:45** ("The mold is what matters"): Mold/table remains glowing, caption

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <EngineeringGrid spacing={40} color="#1E293B" opacity={0.03} />

    {/* Mold diagram with flow — slides left and shrinks */}
    <Animated
      from={{ x: 960, y: 500, scale: 1 }}
      to={{ x: 350, y: 500, scale: 0.5 }}
      startFrame={60} duration={40}>
      <MoldCrossSection
        wallColor="#D9944A" nozzleColor="#4A90D9"
        cavityColor="#5AAA6E" allGlowing>
        <FlowAnimation
          input={{ type: 'text', color: '#4A90D9' }}
          grounding={{ tint: '#5AAA6E' }}
          walls={{ flash: '#D9944A' }}
          output={{ type: 'code', color: '#E2E8F0' }}
        />
      </MoldCrossSection>
    </Animated>

    {/* Summary Table */}
    <Sequence from={60}>
      <DataTable
        position={[650, 250]} width={1100} rowHeight={80}
        bgColor="#1E293B" bgOpacity={0.4} rounded={12}
        headers={['COMPONENT', 'ENCODES', 'OWNER']}
        headerStyle={{ font: 'Inter', size: 12, weight: 600,
          color: '#94A3B8', letterSpacing: 2 }}
        columnWidths={[300, 350, 250]}
        dividerColor="#334155" dividerOpacity={0.2}
        rowStagger={40} rowSlideFrom="right">

        <TableRow accentColor="#4A90D9" accentWidth={3}
          appearAt={120}>
          <Cell><ColorDot color="#4A90D9" /><Label text="Prompt"
            color="#4A90D9" weight={600} /></Cell>
          <Cell text="WHAT (intent)" />
          <Cell text="Developer" opacity={0.6} />
        </TableRow>

        <TableRow accentColor="#5AAA6E" accentWidth={3}
          appearAt={160}>
          <Cell><ColorDot color="#5AAA6E" /><Label text="Grounding"
            color="#5AAA6E" weight={600} /></Cell>
          <Cell text="HOW (style)" />
          <Cell text="Automatic" opacity={0.6} />
        </TableRow>

        <TableRow accentColor="#D9944A" accentWidth={4}
          bgWash="#D9944A" bgWashOpacity={0.04}
          appearAt={200} appearDuration={25}>
          <Cell><ColorDot color="#D9944A" /><Label text="Tests"
            color="#D9944A" weight={700} /></Cell>
          <Cell text="CORRECTNESS" weight={700} />
          <Cell text="Accumulated" opacity={0.6} />
        </TableRow>
      </DataTable>
    </Sequence>

    {/* Conflict resolution line */}
    <Sequence from={310}>
      <FadeIn duration={20}>
        <RichText x={1200} y={700} align="center" font="Inter" size={18}
          color="#E2E8F0" opacity={0.8}>
          When these conflict, <Bold color="#D9944A">tests win</Bold>.{' '}
          <Bold color="#D9944A">Always.</Bold>
        </RichText>
        <DrawLine from={[1080, 722]} to={[1320, 722]}
          color="#D9944A" opacity={0.3} width={2} drawDuration={15} />
      </FadeIn>
    </Sequence>

    {/* Code output — glows then fades */}
    <Sequence from={370}>
      <CodeOutput position={[350, 850]} code={outputSnippet}
        font="JetBrains Mono" size={10}
        color="#E2E8F0" opacity={0.6}
        glowColor="#E2E8F0" glowOpacity={0.15}
        glowFadeAt={420} glowFadeDuration={30}
        dimTo={0.2} dimAt={420} dimDuration={20} />
    </Sequence>

    {/* Final caption */}
    <Sequence from={450}>
      <FadeIn duration={15}>
        <Text text="The code is output. The mold is what matters."
          font="Inter" size={14} color="#D9944A" opacity={0.7}
          x={960} y={1000} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "summary_table",
  "tableId": "three_components",
  "rows": [
    {
      "component": "Prompt",
      "encodes": "WHAT (intent)",
      "owner": "Developer",
      "color": "#4A90D9"
    },
    {
      "component": "Grounding",
      "encodes": "HOW (style)",
      "owner": "Automatic",
      "color": "#5AAA6E"
    },
    {
      "component": "Tests",
      "encodes": "CORRECTNESS",
      "owner": "Accumulated",
      "color": "#D9944A",
      "emphasized": true
    }
  ],
  "conflictRule": "When these conflict, tests win. Always.",
  "hierarchy": ["Tests", "Prompt", "Grounding"],
  "closingLine": "The code is output. The mold is what matters.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_010"]
}
```

---
