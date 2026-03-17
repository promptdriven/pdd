[Remotion]

# Section 6.3: Module Highlight & Update — Extracting a Prompt from Existing Code

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 23:24 - 23:32

## Visual Description

From the dense brownfield codebase of the previous shot, a single module block highlights — it pulses with a blue selection glow, rising above the surrounding gray mass. A label appears: `auth_handler.py`. This is the starting point.

In the bottom-right corner, a subtle terminal appears. The command `pdd update auth_handler.py` types in and executes. As the command runs, the selected module block begins a transformation: from the code block, luminous blue particles stream upward and to the right, coalescing into a new glowing document — a `.prompt` file. The prompt file materializes beside the code block, rendered as a clean document with ~12 lines of readable natural language.

The terminal shows the process completing: the prompt file `auth_handler.prompt` is created. The animation captures the core mechanic — PDD can create prompts *from* existing code, not just the other way around.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Codebase (carried over, dimmed)
- Same topology from 02, but dimmed to 0.3 overall opacity
- All blocks: `#1E293B` at 0.3, edges `#334155` at 0.08

#### Selected Module Block
- Position: (640, 420), size: 120×60px
- Fill: `#1E293B` with selection glow `#4A90D9` at 0.15
- Border: `#4A90D9` at 0.4, 2px
- Outer glow: 20px Gaussian blur, `#4A90D9` at 0.12
- Label: `auth_handler.py` — JetBrains Mono, 11px, `#E2E8F0` at 0.7, centered below block

#### Prompt Document (materializes)
- Position: (1100, 380), size: 280×200px
- Window chrome: 20px title bar, `#1E293B`, rounded top corners 6px
- Title bar text: `auth_handler.prompt` — JetBrains Mono, 10px, `#4A90D9` at 0.6
- Editor background: `#0F172A`
- Content: 12 lines of natural language, Inter, 9px, `#CBD5E1` at 0.6
  - Line 1: `# Auth Handler`
  - Line 2: `Authenticate incoming requests using JWT.`
  - Line 3: `Validate token signature and expiration.`
  - Line 4: `Extract user_id and role from claims.`
  - Line 5: `Return None on invalid or expired tokens.`
  - Lines 6-12: additional constraints and edge cases
- Blue ambient glow: `#4A90D9` at 0.06, 16px blur around entire document
- The glow marks this as specification — where value now lives

#### Particle Stream
- 20-30 small particles (3px circles, `#4A90D9` at 0.3-0.6)
- Flow from code block center (640, 420) to prompt document center (1100, 380)
- Curved Bezier path arcing upward
- Particles vary in speed and opacity — organic, not mechanical

#### Terminal (bottom-right corner)
- Position: (1400, 860), size: 420×140px
- Background: `#0F172A` at 0.85, rounded 6px
- Font: JetBrains Mono, 10px, `#94A3B8` at 0.5
- Line 1: `$ pdd update auth_handler.py`
- Line 2: `Analyzing module... extracting intent...`
- Line 3: `✓ Created auth_handler.prompt`

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Codebase from previous shot dims to 0.3 opacity. Single module block pulses with blue selection glow.
2. **Frame 20-40 (0.67-1.33s):** `auth_handler.py` label appears below selected block. Terminal fades in.
3. **Frame 40-70 (1.33-2.33s):** Terminal command types: `pdd update auth_handler.py`. Cursor blinks.
4. **Frame 70-80 (2.33-2.67s):** Terminal shows "Analyzing module..." — processing begins.
5. **Frame 80-160 (2.67-5.33s):** Particle stream flows from code block to right side. Prompt document frame materializes. Lines of natural language appear one by one inside the prompt document as particles arrive.
6. **Frame 160-180 (5.33-6s):** Terminal shows `✓ Created auth_handler.prompt`. Prompt document fully visible with blue glow.
7. **Frame 180-240 (6-8s):** Hold. The code block and prompt document sit side by side. The prompt glows (specification). The code block is neutral (artifact). The relationship is clear.

### Typography
- Module label: JetBrains Mono, 11px, `#E2E8F0` at 0.7
- Prompt filename: JetBrains Mono, 10px, `#4A90D9` at 0.6
- Prompt content: Inter, 9px, `#CBD5E1` at 0.6
- Terminal: JetBrains Mono, 10px, `#94A3B8` at 0.5
- Terminal success: JetBrains Mono, 10px, `#5AAA6E` at 0.6

### Easing
- Codebase dim: `easeOut(quad)` over 20 frames
- Selection glow: `easeInOut(sine)` pulse on 30-frame cycle
- Terminal fade-in: `easeOut(quad)` over 15 frames
- Command typing: `linear`, 3 characters per frame
- Particle flow: `easeInOut(cubic)` along Bezier, staggered 3 frames apart
- Prompt lines appear: `easeOut(quad)`, 8 frames per line, staggered
- Document glow: `easeOut(cubic)` over 20 frames

## Narration Sync
> "PDD can create prompts from existing code. Start with one module. Generate its prompt. Add tests. Regenerate. Compare."

Segment: `where_to_start_002`

- **23:24** ("PDD can create prompts from existing code"): Module highlights, terminal command begins
- **23:27** ("Start with one module"): `auth_handler.py` label visible, particle stream begins
- **23:29** ("Generate its prompt"): Prompt document materializing, lines appearing
- **23:31** ("Add tests. Regenerate. Compare."): Prompt fully visible, terminal shows success

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Dimmed codebase background */}
    <Opacity value={0.3}>
      <CodebaseGraph blocks={fileBlocks} edges={dependencyEdges}
        blockFill="#1E293B" edgeColor="#334155" edgeOpacity={0.08} />
    </Opacity>

    {/* Selected module with glow */}
    <Sequence from={0}>
      <PulsingGlow color="#4A90D9" opacity={0.12} blur={20} period={30}>
        <CodeBlock position={[640, 420]} size={[120, 60]}
          fill="#1E293B" border={{ color: '#4A90D9', opacity: 0.4, width: 2 }}
          glow={{ color: '#4A90D9', opacity: 0.15 }} />
      </PulsingGlow>
    </Sequence>

    {/* Module label */}
    <Sequence from={20}>
      <FadeIn duration={15}>
        <Text text="auth_handler.py" font="JetBrains Mono" size={11}
          color="#E2E8F0" opacity={0.7} x={640} y={460} align="center" />
      </FadeIn>
    </Sequence>

    {/* Particle stream */}
    <Sequence from={80}>
      <ParticleStream
        from={[640, 420]} to={[1100, 380]}
        count={25} particleSize={3} color="#4A90D9"
        opacityRange={[0.3, 0.6]}
        path="bezier" arcHeight={-120}
        stagger={3} travelDuration={40} />
    </Sequence>

    {/* Prompt document materializing */}
    <Sequence from={100}>
      <EditorWindow position={[960, 280]} size={[280, 200]}
        filename="auth_handler.prompt"
        titleBarColor="#1E293B" editorBg="#0F172A"
        glow={{ color: '#4A90D9', opacity: 0.06, blur: 16 }}>
        <StaggeredLines lines={promptLines}
          font="Inter" fontSize={9} color="#CBD5E1" opacity={0.6}
          lineDelay={8} />
      </EditorWindow>
    </Sequence>

    {/* Terminal */}
    <Sequence from={20}>
      <FadeIn duration={15}>
        <Terminal position={[1400, 860]} size={[420, 140]}
          bg="#0F172A" bgOpacity={0.85}>
          <Sequence from={20}>
            <TypedText text="$ pdd update auth_handler.py"
              font="JetBrains Mono" size={10} color="#94A3B8"
              charsPerFrame={3} />
          </Sequence>
          <Sequence from={50}>
            <FadeIn duration={8}>
              <Text text="Analyzing module... extracting intent..."
                font="JetBrains Mono" size={10} color="#94A3B8"
                opacity={0.4} />
            </FadeIn>
          </Sequence>
          <Sequence from={140}>
            <FadeIn duration={8}>
              <Text text="✓ Created auth_handler.prompt"
                font="JetBrains Mono" size={10} color="#5AAA6E"
                opacity={0.6} />
            </FadeIn>
          </Sequence>
        </Terminal>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "workflow_animation",
  "workflow": "pdd_update",
  "sourceFile": "auth_handler.py",
  "outputFile": "auth_handler.prompt",
  "promptLines": [
    "# Auth Handler",
    "Authenticate incoming requests using JWT.",
    "Validate token signature and expiration.",
    "Extract user_id and role from claims.",
    "Return None on invalid or expired tokens."
  ],
  "terminalCommands": [
    "pdd update auth_handler.py",
    "✓ Created auth_handler.prompt"
  ],
  "particleStream": {
    "from": [640, 420],
    "to": [1100, 380],
    "count": 25
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_002"]
}
```

---
