[Remotion]

# Section 3.9: Three Components — Summary Table and Hierarchy

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 15:03 - 15:21

## Visual Description
The three components come together in a unified visualization. First, an animated pipeline shows the flow: prompt flows in → passes through grounding → fills the mold → constrained by test walls → code emerges. Then a clean data table materializes showing the role of each component: Prompt encodes WHAT (intent), Grounding encodes HOW (style), Tests encode CORRECTNESS. Below the table, a pulsing priority rule appears: "When these conflict, tests win. Always." The final beat shows generated code glowing briefly — then the glow transfers to the mold, driving home the message: "The code is output. The mold is what matters."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Unified Pipeline (top half, Y=80 to Y=450):**
  - Stage 1: Prompt document icon at X=200, `#4A90D9`, label "Prompt" below
  - Arrow → Stage 2: Grounding database icon at X=500, `#5AAA6E`, label "Grounding" below
  - Arrow → Stage 3: Mold cavity with walls at X=800, `#D9944A` walls, label "Tests" below
  - Arrow → Stage 4: Code output block at X=1150, `rgba(255,255,255,0.3)`, label "Code" below
  - Animated flow: Blue particles travel along the arrow path, picking up green tint at grounding stage, being shaped at mold stage, emerging as code
- **Component Table (center, Y=480 to Y=700):**
  - 3 rows × 3 columns, clean design, 900px wide centered
  - Header row: "Component" | "Encodes" | "Owner" — `#FFFFFF` at 0.6 opacity, 16px bold, underline `rgba(255,255,255,0.1)`
  - Row 1: "Prompt" (blue `#4A90D9`) | "WHAT (intent)" | "Developer"
  - Row 2: "Grounding" (green `#5AAA6E`) | "HOW (style)" | "Automatic"
  - Row 3: "Tests" (amber `#D9944A`) | "CORRECTNESS" | "Accumulated"
  - Cell text: 18px, regular (400)
  - Subtle row dividers: `rgba(255,255,255,0.05)`
- **Priority Rule (below table, Y=740):**
  - Text: "When these conflict, tests win. Always." — `#D9944A`, 22px bold
  - Subtle underline pulse in amber
- **Final Beat (bottom, Y=850):**
  - Small code block (150px wide) glowing `rgba(255,255,255,0.3)` → glow transfers leftward to mold icon (150px wide) which glows `#D9944A`
  - Text: "The code is output. The mold is what matters." — `#FFFFFF`, 20px semi-bold

### Animation Sequence
1. **Frame 0-60 (0-2.0s):** Pipeline stages appear left-to-right (15-frame stagger). Each icon fades in with slight upward drift (10px). Labels appear below each
2. **Frame 60-150 (2.0-5.0s):** Animated particle flow through the pipeline — blue particles emerge from prompt, pick up green tint at grounding, enter mold cavity, emerge as code output. Flow is continuous, looping
3. **Frame 150-190 (5.0-6.33s):** Pipeline dims to 0.3 opacity. Table begins to materialize — header row draws in (left-to-right underline)
4. **Frame 190-300 (6.33-10.0s):** Table rows appear with 25-frame stagger:
   - Row 1 (Prompt): Blue text slides in, "WHAT (intent)" fades in, "Developer" fades in
   - Row 2 (Grounding): Green text slides in, "HOW (style)" fades in, "Automatic" fades in
   - Row 3 (Tests): Amber text slides in, "CORRECTNESS" fades in, "Accumulated" fades in
5. **Frame 300-370 (10.0-12.33s):** Priority rule fades in below table. "tests win" portion is emphasized (slightly larger, amber color). Underline pulse animation
6. **Frame 370-450 (12.33-15.0s):** Final beat — code block glows briefly, then glow transfers (animated light sweep moving leftward) to the mold icon. Code block dims to near-invisible. Mold icon glows prominently
7. **Frame 450-500 (15.0-16.67s):** "The code is output. The mold is what matters." text fades in centered below
8. **Frame 500-540 (16.67-18.0s):** Hold at final state. Mold continues ambient glow

### Typography
- Pipeline Labels: Inter, 16px, semi-bold (600), respective component colors
- Table Header: Inter, 16px, bold (700), `#FFFFFF` at 0.6 opacity
- Table Cells: Inter, 18px, regular (400), `#FFFFFF` or respective component color
- Priority Rule: Inter, 22px, bold (700), `#D9944A`
- Final Text: Inter, 20px, semi-bold (600), `#FFFFFF`

### Easing
- Pipeline stage appear: `easeOut(quad)`
- Particle flow: `linear` (constant)
- Table row slide: `easeOut(cubic)`
- Priority rule fade: `easeOut(quad)`
- Glow transfer: `easeInOut(cubic)`
- Final text fade: `easeOut(quad)`

## Narration Sync
> "Prompt plus tests plus grounding. Intent plus constraints plus style. Together, they form a complete specification."
> "When these conflict, tests win. Always. The walls override the specification. The specification overrides the style."
> "The code is output. The mold is what matters."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  {/* Pipeline */}
  <Sequence from={0} durationInFrames={150}>
    <Pipeline
      stages={[
        { icon: "document", label: "Prompt", color: "#4A90D9", x: 200 },
        { icon: "database", label: "Grounding", color: "#5AAA6E", x: 500 },
        { icon: "mold", label: "Tests", color: "#D9944A", x: 800 },
        { icon: "code", label: "Code", color: "rgba(255,255,255,0.3)", x: 1150 }
      ]}
      stagger={15}
    />
    <ParticleFlow path="pipeline" loop={true} />
  </Sequence>

  {/* Table */}
  <Sequence from={150} durationInFrames={150}>
    <ComponentTable
      headers={["Component", "Encodes", "Owner"]}
      rows={[
        { component: "Prompt", componentColor: "#4A90D9", encodes: "WHAT (intent)", owner: "Developer" },
        { component: "Grounding", componentColor: "#5AAA6E", encodes: "HOW (style)", owner: "Automatic" },
        { component: "Tests", componentColor: "#D9944A", encodes: "CORRECTNESS", owner: "Accumulated" }
      ]}
      rowStagger={25}
    />
  </Sequence>

  {/* Priority Rule */}
  <Sequence from={300} durationInFrames={70}>
    <PriorityRule text="When these conflict, tests win. Always." emphasisColor="#D9944A" />
  </Sequence>

  {/* Glow Transfer */}
  <Sequence from={370} durationInFrames={80}>
    <GlowTransfer from="code" to="mold" />
  </Sequence>

  {/* Final Text */}
  <Sequence from={450} durationInFrames={50}>
    <EmphasisText text="The code is output. The mold is what matters." y={850} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "pipeline": {
    "stages": [
      { "id": "prompt", "label": "Prompt", "color": "#4A90D9", "icon": "document" },
      { "id": "grounding", "label": "Grounding", "color": "#5AAA6E", "icon": "database" },
      { "id": "tests", "label": "Tests", "color": "#D9944A", "icon": "mold" },
      { "id": "code", "label": "Code", "color": "rgba(255,255,255,0.3)", "icon": "code" }
    ]
  },
  "table": {
    "headers": ["Component", "Encodes", "Owner"],
    "rows": [
      { "component": "Prompt", "color": "#4A90D9", "encodes": "WHAT (intent)", "owner": "Developer" },
      { "component": "Grounding", "color": "#5AAA6E", "encodes": "HOW (style)", "owner": "Automatic" },
      { "component": "Tests", "color": "#D9944A", "encodes": "CORRECTNESS", "owner": "Accumulated" }
    ]
  },
  "priorityRule": {
    "text": "When these conflict, tests win. Always.",
    "color": "#D9944A"
  }
}
```

---
