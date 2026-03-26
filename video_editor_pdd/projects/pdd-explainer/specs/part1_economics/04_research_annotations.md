[Remotion]

# Section 1.4: Research Annotations — Studies Overlaid on Chart

**Tool:** Remotion
**Duration:** ~40s (1200 frames @ 30fps)
**Timestamp:** 1:25 - 2:05

## Visual Description

The code cost chart from Spec 03 remains visible but the camera has zoomed in slightly on the gap between the solid and dashed amber lines. Research study annotations materialize one by one, each pointing to a specific part of the chart. The annotations are designed like academic citation callouts — clean, precise, grounding the argument in real data.

The sequence builds a damning picture: individual patches get faster (GitHub study), but overall throughput is flat (Uplevel study), and code quality is deteriorating (GitClear study). Each annotation arrives with a small connecting line to its relevant chart element.

After the initial three annotations, two more appear pointing to the debt area: code churn +44% and refactoring -60%. The debt area itself separates into two visible layers: a darker "Code Complexity" layer and a lighter "Context Rot" layer with a subtle static/noise texture.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Inherits chart from Spec 03 (code cost chart)

### Chart/Visual Elements

#### Annotation 1 — GitHub (pointing to dropping solid line)
- Text: "Individual task: −55%" — Inter, 14px, bold, `#2DD4BF`
- Fine print: "GitHub, 2022 · 95 developers, one greenfield task" — Inter, 10px, `#94A3B8` at 0.5
- Connecting line: thin 1px `#2DD4BF` at 0.3 from annotation to solid amber line
- Position: right side of chart, y aligned with solid line ~2023

#### Annotation 2 — Uplevel (pointing to dashed line)
- Text: "Overall throughput: ~0%" — Inter, 14px, bold, `#EF4444`
- Fine print: "Uplevel, 2024 · 785 developers, one year" — Inter, 10px, `#94A3B8` at 0.5
- Connecting line: thin 1px `#EF4444` at 0.3 from annotation to dashed amber line
- Position: right side, y aligned with dashed line

#### Annotation 3 — GitClear (pointing to debt area)
- Text: "Code churn: +44%" — Inter, 14px, bold, `#EF4444`
- Fine print: "GitClear, 2025 · 211M lines analyzed" — Inter, 10px, `#94A3B8` at 0.5
- Connecting line: to debt shaded area
- Position: middle-right, pointing into the shaded region

#### Annotation 4 — Refactoring (pointing to widening gap)
- Text: "Refactoring: −60%" — Inter, 14px, bold, `#EF4444`
- Fine print: below annotation 3
- Position: below annotation 3, also pointing to debt area

#### Debt Layer Separation
- Lower layer: "Code Complexity" — darker amber `#D9944A` at 0.12, solid fill
- Upper layer: "Context Rot" — lighter amber `#D9944A` at 0.06, with SVG noise texture overlay
- Dividing line between layers: `#D9944A` at 0.15, 1px dashed
- Small labels for each layer: Inter, 10px, `#D9944A` at 0.4

### Animation Sequence
1. **Frame 0-60 (0-2s):** Chart from Spec 03 visible. Slight zoom into the gap region.
2. **Frame 60-180 (2-6s):** Annotation 1 (GitHub −55%) materializes with connecting line to solid amber line.
3. **Frame 180-420 (6-14s):** Annotation 2 (Uplevel ~0%) materializes pointing to dashed line. The contrast with Annotation 1 is stark.
4. **Frame 420-660 (14-22s):** Annotation 3 (GitClear +44% churn) appears, pointing to debt area. Annotation 4 (Refactoring −60%) appears below it.
5. **Frame 660-840 (22-28s):** Debt area separates into two layers. "Code Complexity" darkens. "Context Rot" gets noise texture.
6. **Frame 840-1200 (28-40s):** Camera lingers on the layered debt. "Context Rot" layer pulses with a subtle static effect. Annotation: "Faster patching → faster growth → faster rot" appears.

### Typography
- Annotation main text: Inter, 14px, bold (700), `#2DD4BF` or `#EF4444`
- Fine print: Inter, 10px, `#94A3B8` at 0.5
- Layer labels: Inter, 10px, `#D9944A` at 0.4
- Feedback annotation: Inter, 13px, italic, `#D9944A` at 0.6

### Easing
- Annotation appear: `easeOut(cubic)` over 20 frames, slight 5px slide-in from right
- Connecting line draw: `easeOut(quad)` over 15 frames
- Layer separation: `easeInOut(cubic)` over 30 frames
- Noise texture: continuous, subtle `easeInOut(sine)` shimmer

## Narration Sync
> "GitHub measured a 55% speed improvement for individual tasks..."
> "Uplevel tracked almost 800 developers for a full year... Overall throughput? Statistically indistinguishable from zero."
> "GitClear confirmed it across 211 million lines... code churn jumped 44%... refactoring dropped 60%..."
> "there's a second kind of debt building up that almost nobody talks about..."

Segments: `part1_economics_014`, `part1_economics_015`, `part1_economics_016`, `part1_economics_017`

- **97.46s** ("GitHub measured a 55%"): Annotation 1 materializes
- **111.82s** ("Uplevel tracked almost 800"): Annotation 2 appears, contrast visible
- **136.62s** ("GitClear confirmed it"): Annotations 3 & 4 appear
- **158.50s** ("there's a second kind of debt"): Debt layers separate, Context Rot revealed

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1200}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Inherited chart (zoomed view) */}
    <ZoomedChart chart="code_cost_chart" zoomRegion="debt_gap" zoomLevel={1.3} />

    {/* Annotation 1: GitHub */}
    <Sequence from={60}>
      <SlideIn from="right" distance={5} duration={20}>
        <Annotation
          mainText="Individual task: −55%"
          mainColor="#2DD4BF" mainWeight={700}
          subText="GitHub, 2022 · 95 developers, one greenfield task"
          subColor="#94A3B8" subOpacity={0.5}
          connectTo={{ line: "immediate_patch", x: 2023 }}
          lineColor="#2DD4BF" lineOpacity={0.3}
          position={{ x: 1400, y: 620 }} />
      </SlideIn>
    </Sequence>

    {/* Annotation 2: Uplevel */}
    <Sequence from={180}>
      <SlideIn from="right" distance={5} duration={20}>
        <Annotation
          mainText="Overall throughput: ~0%"
          mainColor="#EF4444" mainWeight={700}
          subText="Uplevel, 2024 · 785 developers, one year"
          subColor="#94A3B8" subOpacity={0.5}
          connectTo={{ line: "total_cost_debt", x: 2024 }}
          lineColor="#EF4444" lineOpacity={0.3}
          position={{ x: 1400, y: 200 }} />
      </SlideIn>
    </Sequence>

    {/* Annotation 3: GitClear churn */}
    <Sequence from={420}>
      <SlideIn from="right" distance={5} duration={20}>
        <Annotation
          mainText="Code churn: +44%"
          mainColor="#EF4444" mainWeight={700}
          subText="GitClear, 2025 · 211M lines analyzed"
          subColor="#94A3B8" subOpacity={0.5}
          connectTo={{ area: "debt_area", x: 2024 }}
          lineColor="#EF4444" lineOpacity={0.3}
          position={{ x: 1400, y: 380 }} />
      </SlideIn>
    </Sequence>

    {/* Annotation 4: Refactoring */}
    <Sequence from={480}>
      <SlideIn from="right" distance={5} duration={20}>
        <Annotation
          mainText="Refactoring: −60%"
          mainColor="#EF4444" mainWeight={700}
          connectTo={{ area: "debt_area", x: 2023 }}
          lineColor="#EF4444" lineOpacity={0.3}
          position={{ x: 1400, y: 440 }} />
      </SlideIn>
    </Sequence>

    {/* Debt layer separation */}
    <Sequence from={660}>
      <DebtLayers
        lower={{ label: "Code Complexity", color: "#D9944A", opacity: 0.12 }}
        upper={{ label: "Context Rot", color: "#D9944A", opacity: 0.06, noiseTexture: true }}
        separationDuration={30} />
    </Sequence>

    {/* Feedback annotation */}
    <Sequence from={840}>
      <FadeIn duration={20}>
        <Text text="Faster patching → faster growth → faster rot"
          font="Inter" size={13} style="italic"
          color="#D9944A" opacity={0.6}
          x={960} y={950} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "annotated_chart_overlay",
  "baseChart": "code_cost_chart",
  "annotations": [
    {
      "id": "github_individual",
      "text": "Individual task: −55%",
      "source": "GitHub, 2022",
      "detail": "95 developers, one greenfield task",
      "color": "#2DD4BF",
      "pointsTo": "immediate_patch_line"
    },
    {
      "id": "uplevel_throughput",
      "text": "Overall throughput: ~0%",
      "source": "Uplevel, 2024",
      "detail": "785 developers, one year",
      "color": "#EF4444",
      "pointsTo": "total_cost_dashed_line"
    },
    {
      "id": "gitclear_churn",
      "text": "Code churn: +44%",
      "source": "GitClear, 2025",
      "detail": "211M lines analyzed",
      "color": "#EF4444",
      "pointsTo": "debt_area"
    },
    {
      "id": "refactoring_decline",
      "text": "Refactoring: −60%",
      "source": "GitClear, 2025",
      "color": "#EF4444",
      "pointsTo": "debt_area"
    }
  ],
  "debtLayers": [
    { "id": "code_complexity", "label": "Code Complexity", "opacity": 0.12 },
    { "id": "context_rot", "label": "Context Rot", "opacity": 0.06, "texture": "noise" }
  ],
  "narrationSegments": ["part1_economics_014", "part1_economics_015", "part1_economics_016", "part1_economics_017"]
}
```

---
