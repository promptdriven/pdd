[Remotion]

# Section 3.7: Five Generations + Z3 — Generate, Select, Prove

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 14:05 - 14:23

## Visual Description

Two distinct visual beats in one spec, connected by the theme of reliability despite imperfection.

**Beat 1 — Five Generations (frames 0-300):** Five code panels appear side by side like film frames or contact sheets, evenly spaced across the screen. Each panel contains a simplified code snippet (syntax-highlighted, partially visible). They generate simultaneously — code characters typing in all five panels at once, each producing slightly different output.

As they complete, a test suite runs against each. Two panels get red X overlay marks — they failed tests. Two get yellow warning triangles — they passed but with issues. One glows green with a bright checkmark — it passes all tests. The green panel enlarges slightly and slides to center focus. Below: "Generate five. Pick the one that passes all tests."

The message: perfection on every run isn't needed. The walls (tests) do the selection.

**Beat 2 — Z3 Formal Proof (frames 300-540):** A brief, powerful sidebar. The screen transitions to a darker, more technical view. A mathematical proof notation appears — clean, formal, intimidating but beautiful. The Z3 logo materializes alongside the Synopsys Formality logo. A label reads: "Same class of SMT solver used in chip verification."

A single property is shown being proven: "∀ input: parse(input) ∈ {Valid(id), None}" — with a "PROVEN ✓" stamp in green. The annotation reads: "Not sampling. Mathematical proof. The chip design analogy isn't a metaphor. It's the same technology."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: subtle dot grid, 30px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Beat 1 — Five Code Panels

**Panel Layout (y: 180-680)**
- 5 panels, each 300w × 500h, spaced 20px apart
- Starting x: 110, 430, 750, 1070, 1390
- Background: `#1E293B` at 0.6, 1px `#334155` border, rounded 6px
- Title bar: 30px, `#0F172A`, with filename: `user_parser_v{N}.py`

**Code Content (per panel)**
- Font: JetBrains Mono, 10px
- Syntax highlighting: keywords `#C792EA`, strings `#C3E88D`, functions `#82AAFF`, comments `#546E7A`
- Each panel shows slightly different code — different variable names, different structure
- Code typing speed: 2 frames per character, staggered start (5 frames between panels)

**Test Results**
- Panel 1: Red X overlay, `#EF4444` at 0.6, 80px, centered — "2 tests failed"
- Panel 2: Yellow triangle, `#D9944A` at 0.6, 60px — "Performance warning"
- Panel 3: Green checkmark, `#5AAA6E` at 0.8, 80px — "All 12 tests pass ✓"
- Panel 4: Red X overlay — "Null handling error"
- Panel 5: Yellow triangle — "Style violations"

**Winner Highlight**
- Panel 3 border: `#5AAA6E` at 0.6, 2px glow, 8px blur
- Scale: 1.05× with slight z-lift shadow
- Other panels: dim to 0.3 opacity

**Caption**
- "Generate five. Pick the one that passes all tests." — Inter, 16px, `#E2E8F0` at 0.7, centered at y: 780
- "The walls don't care how many attempts it took." — Inter, 13px, `#64748B` at 0.5, centered at y: 820

#### Beat 2 — Z3 Formal Proof

**Proof Notation (centered, y: 300-600)**
- Mathematical expression: "∀ input ∈ String:" — JetBrains Mono, 24px, `#C792EA`
- Property: "parse(input) ∈ {Valid(id), None}" — JetBrains Mono, 20px, `#82AAFF`
- Proof steps (simplified, 3 lines): JetBrains Mono, 14px, `#94A3B8` at 0.5
- "PROVEN ✓" stamp: Inter, 36px, bold (700), `#5AAA6E`, with 2px border, angled 5°

**Logos**
- Z3 logo: positioned at (400, 200), 60px, `#94A3B8` at 0.5
- Synopsys Formality logo: positioned at (560, 200), 60px, `#94A3B8` at 0.5
- Connecting label: "Same class of SMT solver" — Inter, 11px, `#64748B` at 0.5

**Annotation**
- "Not sampling. Mathematical proof." — Inter, 16px, bold (700), `#E2E8F0` at 0.8, y: 700
- "The chip design analogy isn't a metaphor. It's the same technology." — Inter, 13px, `#D9944A` at 0.6, y: 740

### Animation Sequence
1. **Frame 0-30 (0-1s):** Five empty panels appear, staggered (5 frames apart), borders draw.
2. **Frame 30-120 (1-4s):** Code types simultaneously in all five panels. Different code in each. Syntax highlighting as characters appear.
3. **Frame 120-180 (4-6s):** Test run animation — a progress bar sweeps across each panel. Results appear staggered: X, △, ✓, X, △. Each result has a brief flash effect.
4. **Frame 180-240 (6-8s):** Panel 3 (green) enlarges to 1.05×. Others dim to 0.3. Green glow and shadow appear. Winner slides very slightly toward center.
5. **Frame 240-300 (8-10s):** Caption appears: "Generate five. Pick the one that passes all tests." Sub-caption follows.

6. **Frame 300-330 (10-11s):** Cross-dissolve transition. Five panels fade out. Background darkens.
7. **Frame 330-390 (11-13s):** Z3 and Synopsys logos fade in. "Same class of SMT solver" label appears.
8. **Frame 390-450 (13-15s):** Mathematical proof notation types in — formal, precise. Each line appears with slight stagger.
9. **Frame 450-480 (15-16s):** "PROVEN ✓" stamp slams in with spring animation, angled. Green flash.
10. **Frame 480-540 (16-18s):** Annotation text appears. Hold. The technology claim lands.

### Typography
- Panel filenames: JetBrains Mono, 10px, `#94A3B8` at 0.6
- Code: JetBrains Mono, 10px, syntax-highlighted
- Test result labels: Inter, 11px, respective colors
- Caption: Inter, 16px, `#E2E8F0` at 0.7
- Sub-caption: Inter, 13px, `#64748B` at 0.5
- Math notation: JetBrains Mono, 20-24px, `#C792EA` / `#82AAFF`
- Proof stamp: Inter, 36px, bold (700), `#5AAA6E`
- Annotation: Inter, 13-16px, `#E2E8F0` / `#D9944A`

### Easing
- Panel appear: `easeOut(quad)` over 12 frames, 5-frame stagger
- Code typing: `linear`, 2 frames/char
- Test result flash: `easeOut(expo)` over 8 frames
- Winner scale: `spring({ stiffness: 150, damping: 14 })` to 1.05
- Dim others: `easeOut(quad)` over 20 frames to 0.3
- Cross-dissolve: `easeInOut(quad)` over 30 frames
- Proof stamp: `spring({ stiffness: 300, damping: 8 })` scale from 1.5 to 1.0
- Logo fade: `easeOut(quad)` over 20 frames

## Narration Sync
> "Now — you might be thinking: 'But LLMs don't follow instructions reliably.' You're right. Today. But PDD doesn't need perfection on every run. Generate five versions. Pick the one that passes all tests. The walls don't care how many attempts it took."
> "And some of those walls aren't just tested — they're proven. PDD uses Z3, the same class of SMT solver that the chip industry uses for formal equivalence checking, to mathematically prove that properties hold for every possible input. Not sampling. Mathematical proof."

Segment: `part3_007`

- **14:05** ("But LLMs don't follow instructions reliably"): Five panels appear, code generating
- **14:10** ("Generate five versions"): Test results appear — X, △, ✓, X, △
- **14:13** ("Pick the one that passes all tests"): Winner highlighted, caption
- **14:16** ("some of those walls aren't just tested — they're proven"): Z3 section begins
- **14:19** ("the same class of SMT solver"): Logos, math notation
- **14:22** ("Mathematical proof"): PROVEN stamp, annotation

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <DotGrid spacing={30} color="#1E293B" opacity={0.03} />

    {/* Beat 1: Five Generations */}
    <Sequence from={0} durationInFrames={300}>
      {[0, 1, 2, 3, 4].map((i) => (
        <Sequence key={i} from={i * 5}>
          <CodePanel
            x={110 + i * 320} y={180} width={300} height={500}
            filename={`user_parser_v${i + 1}.py`}
            code={codeVariants[i]}
            typeSpeed={2}
            testResult={testResults[i]}
            testAppearAt={120}
            isWinner={i === 2}
            winnerHighlightAt={180}
            dimAt={i !== 2 ? 180 : undefined}
          />
        </Sequence>
      ))}

      <Sequence from={240}>
        <FadeIn duration={20}>
          <Text text="Generate five. Pick the one that passes all tests."
            font="Inter" size={16} color="#E2E8F0" opacity={0.7}
            x={960} y={780} align="center" />
          <Text text="The walls don't care how many attempts it took."
            font="Inter" size={13} color="#64748B" opacity={0.5}
            x={960} y={820} align="center" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Beat 2: Z3 Formal Proof */}
    <Sequence from={300}>
      <CrossDissolve duration={30}>
        <AbsoluteFill style={{ backgroundColor: '#080C16' }}>
          {/* Logos */}
          <Sequence from={30}>
            <FadeIn duration={20}>
              <Logo src="/logos/z3.svg" position={[400, 200]} size={60} />
              <Logo src="/logos/synopsys.svg" position={[560, 200]} size={60} />
              <Text text="Same class of SMT solver"
                font="Inter" size={11} color="#64748B" opacity={0.5}
                x={480} y={270} align="center" />
            </FadeIn>
          </Sequence>

          {/* Proof notation */}
          <Sequence from={60}>
            <TypeWriter text="∀ input ∈ String:"
              font="JetBrains Mono" size={24} color="#C792EA"
              charDelay={3} x={960} y={380} align="center" />
          </Sequence>
          <Sequence from={90}>
            <TypeWriter text="parse(input) ∈ {Valid(id), None}"
              font="JetBrains Mono" size={20} color="#82AAFF"
              charDelay={2} x={960} y={440} align="center" />
          </Sequence>

          {/* PROVEN stamp */}
          <Sequence from={150}>
            <SpringScale stiffness={300} damping={8} from={1.5}>
              <ProofStamp text="PROVEN ✓" color="#5AAA6E"
                size={36} angle={5} x={960} y={550} />
            </SpringScale>
          </Sequence>

          {/* Annotation */}
          <Sequence from={180}>
            <FadeIn duration={20}>
              <Text text="Not sampling. Mathematical proof."
                font="Inter" size={16} weight={700}
                color="#E2E8F0" opacity={0.8}
                x={960} y={700} align="center" />
              <Text text="The chip design analogy isn't a metaphor. It's the same technology."
                font="Inter" size={13} color="#D9944A" opacity={0.6}
                x={960} y={740} align="center" />
            </FadeIn>
          </Sequence>
        </AbsoluteFill>
      </CrossDissolve>
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
      "id": "five_generations",
      "type": "code_panel_array",
      "panelCount": 5,
      "testResults": [
        { "panel": 1, "result": "fail", "reason": "2 tests failed" },
        { "panel": 2, "result": "warning", "reason": "Performance warning" },
        { "panel": 3, "result": "pass", "reason": "All 12 tests pass", "winner": true },
        { "panel": 4, "result": "fail", "reason": "Null handling error" },
        { "panel": 5, "result": "warning", "reason": "Style violations" }
      ],
      "caption": "Generate five. Pick the one that passes all tests."
    },
    {
      "id": "z3_formal_proof",
      "type": "proof_notation",
      "property": "∀ input ∈ String: parse(input) ∈ {Valid(id), None}",
      "solver": "Z3 SMT Solver",
      "comparison": "Synopsys Formality — chip verification",
      "result": "PROVEN",
      "annotation": "Not sampling. Mathematical proof."
    }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_007"]
}
```

---
