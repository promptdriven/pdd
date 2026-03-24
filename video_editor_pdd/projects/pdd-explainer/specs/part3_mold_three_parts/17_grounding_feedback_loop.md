[Remotion]

# Section 3.17: Grounding Feedback Loop — Learning From Success

**Tool:** Remotion
**Duration:** ~22s (660 frames @ 30fps)
**Timestamp:** 5:04 - 5:26

## Visual Description

A diagram showing the grounding feedback loop. The flow starts with a prompt and tests generating code. When the code passes all tests (green checkmark), the successful (prompt, code) pair flows into a "Grounding Database" — a glowing repository. Future generations then pull from this database, inheriting the patterns, style, and conventions.

**Phase 1:** Same prompt with two different grounding contexts produces different code:
- Path A: OOP grounding → generates classes with methods (blue-tinted code)
- Path B: Functional grounding → generates pure functions with composition (green-tinted code)
Both pass all tests.

**Phase 2:** A successful generation (green glow) flows into the Grounding Database. An arrow shows `(prompt, code)` pair flowing to a cloud storage icon. Future generations now pull from this enriched database.

**Phase 3:** Pull back to see all three components working together: Prompt flows in → passes through grounding → fills the mold → constrained by test walls → code emerges.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Phase 1 — Dual Grounding Paths
- Prompt node (top center): rounded rect 200×60px, `#2DD4BF` border, centered at (960, 100)
- Branch left (OOP): arrow to code panel at (350, 350), code panel tinted `#4A90D9`
  - Label: "OOP grounding" — Inter, 12px, `#4A90D9`
  - Code shows: `class UserParser:` with methods
- Branch right (Functional): arrow to code panel at (1570, 350), code panel tinted `#4ADE80`
  - Label: "Functional grounding" — Inter, 12px, `#4ADE80`
  - Code shows: `def parse_user(input):` with composition
- Both panels: green checkmark `#4ADE80` at 0.6

#### Phase 2 — Feedback Into Database
- Successful code panel (green glow) at center
- Arrow flowing to "Grounding Database" node at (960, 650)
- Database: cylinder shape 200×100px, `#A78BFA` at 0.2 fill, `#A78BFA` at 0.5 border
- Cloud icon: small, `#A78BFA` at 0.4, next to database
- Label pair flowing: `(prompt, code)` — JetBrains Mono, 10px, `#A78BFA` at 0.5
- Future arrow: from database back to generation pipeline

#### Phase 3 — Complete Pipeline
- Left to right flow: Prompt → Grounding → Mold → Test Walls → Code Output
- Each component colored: teal → purple → amber → blue → grey
- Connecting arrows animated left to right

### Animation Sequence
1. **Frame 0-90 (0-3s):** Phase 1 setup — prompt node appears, branches to two paths.
2. **Frame 90-210 (3-7s):** OOP code panel appears with blue tint. Functional code panel appears with green tint. Both get checkmarks.
3. **Frame 210-330 (7-11s):** Phase 2 — successful code glows. Arrow flows to Grounding Database. `(prompt, code)` pair label follows the arrow.
4. **Frame 330-420 (11-14s):** Database glows. Future generation arrow returns. Cloud icon appears.
5. **Frame 420-540 (14-18s):** Phase 3 — all three components visible in pipeline: Prompt → Grounding → Mold → Walls → Code.
6. **Frame 540-660 (18-22s):** Hold. Pipeline pulses left to right. Label: "Prompt plus tests plus grounding. Intent plus constraints plus style."

### Typography
- Path labels: Inter, 12px, respective colors
- Code: JetBrains Mono, 9px, syntax-highlighted with color tint
- Database label: Inter, 14px, bold (700), `#A78BFA`
- Pair label: JetBrains Mono, 10px, `#A78BFA` at 0.5
- Pipeline labels: Inter, 12px, bold, respective component colors
- Bottom label: Inter, 16px, `#E2E8F0` at 0.6

### Easing
- Node appear: `easeOut(cubic)` over 20 frames
- Branch arrows: `easeInOut(cubic)` over 30 frames
- Code panels: `easeOut(quad)` over 20 frames
- Pair flow: `easeInOut(cubic)` over 40 frames — follows arrow path
- Database glow: `easeOut(cubic)` over 30 frames
- Pipeline pulse: `easeInOut(sine)` — wave moving left to right, 60-frame cycle

## Narration Sync
> "Grounding is learned from your past generations. When you successfully generate and fix code, that knowledge feeds back into the system."
> "Your style, your patterns, your team's conventions. Grounding captures all of it and applies it automatically to future generations."
> "Prompt plus tests plus grounding. Intent plus constraints plus style. Together, they form a complete specification."

Segments: `part3_mold_three_parts_026`, `part3_mold_three_parts_027`, `part3_mold_three_parts_028`

- **5:04** ("learned from your past"): Dual grounding paths appear
- **5:14** ("Your style, your patterns"): Feedback arrow to database
- **5:22** ("Prompt plus tests plus grounding"): Complete pipeline visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={660}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.05} />

    {/* Phase 1: Dual grounding paths */}
    <Sequence from={0}>
      <PromptNode x={960} y={100} label="user_parser.prompt"
        color="#2DD4BF" />
    </Sequence>

    <Sequence from={30}>
      <BranchArrow from={[860, 130]} to={[450, 320]} color="#4A90D9" />
      <BranchArrow from={[1060, 130]} to={[1470, 320]} color="#4ADE80" />
    </Sequence>

    <Sequence from={90}>
      <CodePanel x={350} y={350} width={300} height={200}
        tint="#4A90D9" label="OOP grounding"
        code={OOP_CODE} checkmark={true} />
      <CodePanel x={1570} y={350} width={300} height={200}
        tint="#4ADE80" label="Functional grounding"
        code={FUNC_CODE} checkmark={true} />
    </Sequence>

    {/* Phase 2: Feedback to database */}
    <Sequence from={210}>
      <FlowArrow from={[960, 450]} to={[960, 620]}
        color="#A78BFA" label="(prompt, code)"
        flowDuration={40} />
      <Sequence from={60}>
        <DatabaseNode x={960} y={650} label="Grounding Database"
          color="#A78BFA" cloudIcon={true}
          glowDuration={30} />
      </Sequence>
    </Sequence>

    {/* Phase 3: Complete pipeline */}
    <Sequence from={420}>
      <Pipeline
        stages={[
          { label: "Prompt", color: "#2DD4BF" },
          { label: "Grounding", color: "#A78BFA" },
          { label: "Mold", color: "#D9944A" },
          { label: "Test Walls", color: "#4A90D9" },
          { label: "Code", color: "#64748B" }
        ]}
        y={850} pulseSpeed={60} />
    </Sequence>

    {/* Bottom label */}
    <Sequence from={540}>
      <FadeIn duration={20}>
        <Text text="Intent + Constraints + Style = Complete Specification"
          font="Inter" size={16} color="#E2E8F0" opacity={0.6}
          x={960} y={950} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "grounding_feedback_loop",
  "phases": [
    {
      "id": "dual_grounding",
      "paths": [
        { "label": "OOP grounding", "style": "classes_with_methods", "color": "#4A90D9" },
        { "label": "Functional grounding", "style": "pure_functions", "color": "#4ADE80" }
      ]
    },
    {
      "id": "feedback",
      "flow": "(prompt, code) → Grounding Database",
      "color": "#A78BFA"
    },
    {
      "id": "pipeline",
      "stages": ["Prompt", "Grounding", "Mold", "Test Walls", "Code"]
    }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_three_parts_026", "part3_mold_three_parts_027", "part3_mold_three_parts_028"]
}
```

---
