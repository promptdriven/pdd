[Remotion]

# Section 3.12: Prompt Nozzle — The Specification

**Tool:** Remotion
**Duration:** ~24s (720 frames @ 30fps)
**Timestamp:** 3:51 - 4:15

## Visual Description

Return to the mold cross-section. This time the nozzle (injection point at the top) illuminates in amber while the walls dim to low opacity. The nozzle is the prompt — the specification of what you want.

Labels appear around the nozzle: "intent", "requirements", "constraints". These float in from three directions and settle into position, connected to the nozzle via thin amber lines.

Then text flows into the mold like injection material. The text reads: "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode." The text streams character by character from the nozzle into the cavity, becoming the liquid that fills the mold. A file label briefly appears and fades: `user_parser.prompt`.

The prompt doesn't define the walls — it defines what's being asked for. Two regeneration cycles run: the same prompt produces two slightly different code outputs (different variable names, different structure), but both conform to the same walls. A terminal in the corner shows `pdd generate user_parser.prompt` running twice with different outputs.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Mold (nozzle highlighted)
- Walls: `#4A90D9` at 0.1 (dimmed)
- Nozzle: `#D9944A` glow at 0.5, 15px blur
- Cavity: neutral

#### Nozzle Labels
- "intent" — Inter, 16px, semi-bold (600), `#D9944A`, positioned top-left of nozzle
- "requirements" — Inter, 16px, semi-bold (600), `#D9944A`, positioned top-right
- "constraints" — Inter, 16px, semi-bold (600), `#D9944A`, positioned directly above
- Connector lines: `#D9944A` at 0.3, 1px

#### Prompt Text Stream
- Text: "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode."
- Font: JetBrains Mono, 12px, `#D9944A`
- Streams character by character from nozzle opening into cavity
- As text enters cavity, it transforms into the liquid gradient (amber → teal)

#### File Label
- `user_parser.prompt` — JetBrains Mono, 12px, `#D9944A` at 0.5
- Appears briefly near nozzle, fades after 30 frames

#### Dual Generation (split inside cavity)
- Cavity splits vertically with a thin dashed line
- Left half: code version A (JetBrains Mono, 9px, syntax colors)
- Right half: code version B (different variable names, same behavior)
- Both halves constrained by the same walls

#### Terminal
- Bottom-right corner, 400px × 80px
- `$ pdd generate user_parser.prompt` → different output hash each time
- JetBrains Mono, 11px, `#A6E3A1`

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold transition: walls dim, nozzle illuminates amber.
2. **Frame 30-90 (1-3s):** Nozzle labels float in from three directions: "intent", "requirements", "constraints". Connector lines draw.
3. **Frame 90-120 (3-4s):** File label `user_parser.prompt` fades in near nozzle.
4. **Frame 120-240 (4-8s):** Prompt text streams character by character from nozzle into cavity. Characters transform into liquid as they enter. File label fades.
5. **Frame 240-300 (8-10s):** Liquid fills cavity, constrained by walls. First code version visible in left half.
6. **Frame 300-360 (10-12s):** Liquid drains. Terminal: `pdd generate user_parser.prompt` (run 1).
7. **Frame 360-480 (12-16s):** Second injection. Same prompt text. Liquid fills again. Different code version in right half. Terminal: run 2.
8. **Frame 480-600 (16-20s):** Both code versions visible side by side in split cavity. Both conform to walls. Different variable names, same shape.
9. **Frame 600-720 (20-24s):** Hold. The code varies; the behavior is fixed. Walls glow to emphasize they're the constant.

### Typography
- Nozzle labels: Inter, 16px, semi-bold (600), `#D9944A`
- Prompt text: JetBrains Mono, 12px, `#D9944A`
- File label: JetBrains Mono, 12px, `#D9944A` at 0.5
- Code: JetBrains Mono, 9px, syntax colors
- Terminal: JetBrains Mono, 11px, `#A6E3A1`

### Easing
- Nozzle glow: `easeOut(quad)` over 20 frames
- Label float-in: `easeOut(cubic)` over 20 frames each
- Text stream: linear, 2 frames per character
- Liquid transform: `easeInOut(sine)` as characters become liquid
- Drain: `easeIn(quad)` over 20 frames
- Refill: custom bezier over 40 frames

## Narration Sync
> "Second: the prompt. Your specification of what you want. The prompt doesn't define the walls — tests do that. The prompt defines what you're asking for and why. Notice something subtle: the exact implementation can vary. What's locked is the behavior. The code is flexible; the contract is fixed."

Segment: `part3_mold_parts_016`

- **231.14s** (seg 016): Nozzle illuminates — "Second: the prompt"
- **234.0s**: Labels appear — "Your specification"
- **238.0s**: Prompt text streams — "The prompt defines what you're asking for"
- **245.0s**: First generation fills cavity
- **249.0s**: Second generation — "the exact implementation can vary"
- **254.90s** (seg 016 ends): Both versions visible — "the contract is fixed"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={720}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Mold with highlighted nozzle */}
    <MoldCrossSection
      wallsOpacity={0.1} nozzleOpacity={1.0}
      nozzleGlow={{ color: "#D9944A", blur: 15, opacity: 0.5 }}
    />

    {/* Nozzle labels */}
    <Sequence from={30}>
      {NOZZLE_LABELS.map((label, i) => (
        <Sequence key={i} from={i * 15}>
          <FloatIn direction={label.direction} distance={40} duration={20}>
            <ConnectorLabel text={label.text} color="#D9944A"
              font="Inter" size={16} weight={600} />
          </FloatIn>
        </Sequence>
      ))}
    </Sequence>

    {/* File label */}
    <Sequence from={90} durationInFrames={60}>
      <FadeIn duration={15}>
        <FadeOut from={30} duration={15}>
          <Text text="user_parser.prompt" color="#D9944A" opacity={0.5}
            font="JetBrains Mono" size={12} />
        </FadeOut>
      </FadeIn>
    </Sequence>

    {/* Prompt text stream */}
    <Sequence from={120}>
      <TextStream
        text="Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode."
        font="JetBrains Mono" size={12} color="#D9944A"
        charDelay={2}
        transformToLiquid={{ from: "#D9944A", to: "#0D9488" }}
      />
    </Sequence>

    {/* Dual generation */}
    <Sequence from={240}>
      <DualCavity
        versionA={CODE_VERSION_A}
        versionB={CODE_VERSION_B}
        drainFrame={300}
        refillFrame={360}
      />
    </Sequence>

    {/* Terminal */}
    <Sequence from={300}>
      <TerminalWindow x={1450} y={900} width={400} height={80}
        commands={[
          { text: "pdd generate user_parser.prompt", delay: 0 },
          { text: "pdd generate user_parser.prompt", delay: 60 }
        ]}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "prompt_nozzle",
  "nozzleLabels": ["intent", "requirements", "constraints"],
  "promptText": "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.",
  "promptFile": "user_parser.prompt",
  "dualGeneration": true,
  "narrationSegments": ["part3_mold_parts_016"],
  "durationSeconds": 24.0
}
```

---
