[Remotion]

# Section 6.4: Source of Truth Shift — Code Grays, Prompt Glows

**Tool:** Remotion
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 23:32 - 23:38

## Visual Description

A focused two-panel composition shows the critical moment of value migration. On the left, the original `auth_handler.py` code block — previously the authoritative artifact — visually desaturates, its border fading from neutral to gray, its content dimming. On the right, the `auth_handler.prompt` document glows brighter, its blue aura intensifying.

Between them, a subtle animated arrow reverses direction: originally pointing code → prompt (extraction), it now points prompt → code (generation). A label materializes below: **"The prompt is your new source of truth."**

Below the prompt document, three small amber wall icons appear — test constraints. A terminal in the corner shows: `pdd test auth_handler → 3/3 passing`. The regenerated code passes all tests, confirming the prompt is sufficient.

This visual callback to the "Brownfield Absorption" motif (#10 from the design notes) makes the value migration concrete and personal for the viewer.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Code Block (left, desaturating)
- Position: (480, 400), size: 300×200px
- Editor window with title bar: `auth_handler.py`
- Content: 15 lines of code, JetBrains Mono, 9px
- Initial state: `#94A3B8` at 0.5 (visible)
- Final state: `#64748B` at 0.2 (grayed out)
- Border fades from `#334155` at 0.3 to `#334155` at 0.1
- Label below: "artifact" — Inter, 11px, `#64748B` at 0.3, italic

#### Prompt Document (right, glowing)
- Position: (1120, 380), size: 300×220px
- Editor window with title bar: `auth_handler.prompt`
- Content: 12 lines of natural language, Inter, 9px, `#CBD5E1` at 0.7
- Blue ambient glow: intensifies from `#4A90D9` at 0.06 to `#4A90D9` at 0.12
- Border: `#4A90D9` at 0.3, 2px
- Label below: "source of truth" — Inter, 11px, `#4A90D9` at 0.6, bold

#### Direction Arrow
- Curved arrow between the two panels
- Initial: points left → right (code to prompt, extraction)
- Reverses to right → left (prompt to code, generation)
- Arrow color: `#4A90D9` at 0.4
- Arrow head: 8px, filled

#### Test Walls (below prompt)
- 3 small rectangular wall icons, 8×24px each, `#D9944A` at 0.5
- Positioned below prompt document in a row, spaced 20px apart
- Labels below walls: "JWT verify", "expiry check", "null safety" — JetBrains Mono, 7px, `#D9944A` at 0.3

#### Callout Text (centered, bottom)
- "The prompt is your new source of truth." — Inter, 16px, `#E2E8F0` at 0.6
- "source of truth" emphasized in `#4A90D9` at 0.8
- Centered at y: 880

#### Terminal (bottom-right corner)
- Position: (1400, 900), size: 360×80px
- `$ pdd test auth_handler` → `✓ 3/3 passing`
- Success color: `#5AAA6E` at 0.5

### Animation Sequence
1. **Frame 0-30 (0-1s):** Both panels visible from previous shot. Arrow points left → right (extraction direction from prior animation).
2. **Frame 30-70 (1-2.33s):** Code block desaturates — content fades, border dims. Simultaneously, prompt glow intensifies. The visual weight shifts right.
3. **Frame 70-100 (2.33-3.33s):** Arrow reverses direction with a smooth rotation. Now points right → left (generation direction). The relationship has inverted.
4. **Frame 100-120 (3.33-4s):** "artifact" label fades in below code. "source of truth" label fades in below prompt. Three test wall icons appear below prompt.
5. **Frame 120-140 (4-4.67s):** Terminal shows test results: `✓ 3/3 passing`.
6. **Frame 140-180 (4.67-6s):** Callout text appears at bottom. Hold on the complete composition.

### Typography
- Panel labels: Inter, 11px, respective colors
- Callout: Inter, 16px, `#E2E8F0` at 0.6
- Test wall labels: JetBrains Mono, 7px, `#D9944A` at 0.3
- Terminal: JetBrains Mono, 10px, `#94A3B8` at 0.5

### Easing
- Code desaturation: `easeInOut(quad)` over 40 frames
- Prompt glow intensify: `easeInOut(quad)` over 40 frames
- Arrow reverse: `easeInOut(cubic)` rotation over 30 frames
- Label fade-in: `easeOut(quad)` over 15 frames
- Wall icons: `easeOut(cubic)` scale 0 → 1, staggered 5 frames apart
- Callout fade: `easeOut(quad)` over 20 frames

## Narration Sync
> "When the regenerated version passes all tests, the prompt is your new source of truth for that module."

Segment: `where_to_start_002`

- **23:32** ("When the regenerated version"): Code begins desaturating, prompt begins glowing
- **23:34** ("passes all tests"): Test walls appear, terminal shows passing
- **23:36** ("the prompt is your new source of truth"): Arrow reversed, callout text appears
- **23:38** ("for that module"): Hold on complete composition

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Code block — desaturating */}
    <AnimateOpacity from={0.5} to={0.2} duration={40} startFrame={30}>
      <EditorWindow position={[330, 300]} size={[300, 200]}
        filename="auth_handler.py"
        titleBarColor="#1E293B" editorBg="#0F172A">
        <CodeLines lines={authHandlerCode}
          font="JetBrains Mono" fontSize={9} color="#94A3B8" />
      </EditorWindow>
    </AnimateOpacity>
    <Sequence from={100}>
      <FadeIn duration={15}>
        <Text text="artifact" font="Inter" size={11}
          color="#64748B" opacity={0.3} italic
          x={480} y={520} align="center" />
      </FadeIn>
    </Sequence>

    {/* Direction arrow — reverses */}
    <DirectionArrow
      from={[640, 420]} to={[960, 420]}
      color="#4A90D9" opacity={0.4} headSize={8}
      reverseAtFrame={70} reverseDuration={30} />

    {/* Prompt document — intensifying glow */}
    <AnimateGlow from={0.06} to={0.12} duration={40}
      startFrame={30} color="#4A90D9" blur={16}>
      <EditorWindow position={[970, 270]} size={[300, 220]}
        filename="auth_handler.prompt"
        titleBarColor="#1E293B" editorBg="#0F172A"
        border={{ color: '#4A90D9', opacity: 0.3, width: 2 }}>
        <TextLines lines={promptContent}
          font="Inter" fontSize={9} color="#CBD5E1" opacity={0.7} />
      </EditorWindow>
    </AnimateGlow>
    <Sequence from={100}>
      <FadeIn duration={15}>
        <Text text="source of truth" font="Inter" size={11}
          color="#4A90D9" opacity={0.6} weight={700}
          x={1120} y={510} align="center" />
      </FadeIn>
    </Sequence>

    {/* Test walls */}
    <Sequence from={100}>
      <StaggeredScaleIn stagger={5} duration={12}>
        <WallIcon label="JWT verify" color="#D9944A"
          position={[1060, 550]} />
        <WallIcon label="expiry check" color="#D9944A"
          position={[1120, 550]} />
        <WallIcon label="null safety" color="#D9944A"
          position={[1180, 550]} />
      </StaggeredScaleIn>
    </Sequence>

    {/* Terminal */}
    <Sequence from={120}>
      <FadeIn duration={10}>
        <Terminal position={[1400, 900]} size={[360, 80]}>
          <Text text="$ pdd test auth_handler → ✓ 3/3 passing"
            font="JetBrains Mono" size={10} color="#5AAA6E"
            opacity={0.5} />
        </Terminal>
      </FadeIn>
    </Sequence>

    {/* Callout */}
    <Sequence from={140}>
      <FadeIn duration={20}>
        <RichText x={960} y={880} align="center" font="Inter" size={16}
          color="#E2E8F0" opacity={0.6}>
          The prompt is your new{' '}
          <Span color="#4A90D9" opacity={0.8}>source of truth</Span>.
        </RichText>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "value_migration",
  "before": {
    "sourceOfTruth": "auth_handler.py",
    "role": "code",
    "state": "active"
  },
  "after": {
    "sourceOfTruth": "auth_handler.prompt",
    "role": "specification",
    "state": "glowing"
  },
  "tests": [
    { "name": "JWT verify", "status": "passing" },
    { "name": "expiry check", "status": "passing" },
    { "name": "null safety", "status": "passing" }
  ],
  "terminalCommand": "pdd test auth_handler",
  "terminalResult": "3/3 passing",
  "callout": "The prompt is your new source of truth.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_002"]
}
```

---
