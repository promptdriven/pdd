[Remotion]

# Section 1.3: Research Annotations — Stacking the Evidence

**Tool:** Remotion
**Duration:** ~30s (900 frames @ 30fps)
**Timestamp:** 3:27 - 3:57

## Visual Description

Building on the triple-line chart from the previous spec, research annotations materialize one at a time, stacking evidence that faster patching doesn't improve total throughput. Each annotation appears as a clean callout with a connecting line to the relevant part of the chart.

The annotations arrive in three beats:

1. **GitHub/Uplevel contrast** — "Individual task: -55%" points to the dropping solid amber line. "Overall throughput: ~0%" points to the flat dashed line. Fine print beneath each citation. The contrast is immediately visual.

2. **GitClear data** — "Code churn: +44%" and "Refactoring: -60%" appear pointing to the expanding debt shaded area. The picture worsens.

3. **Debt decomposition** — The shaded debt area separates into two visible layers: a darker "Code Complexity" layer and a lighter "Context Rot" layer with a subtle static/noise texture. This introduces the next beat (context window).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117`
- Chart: continues from previous spec (03_code_cost_triple_line)

### Chart/Visual Elements

#### Annotation 1 — GitHub Study
- Callout box: rounded rect, `#1A2332` fill, `#4A90D9` 1px border at 0.3
- Position: right side of chart, pointing to the solid amber line at 2022
- Text: "Individual task: −55%" — Inter, 14px, bold, `#4A90D9` at 0.8
- Subtext: "GitHub, 2022 • 95 devs, one greenfield task" — Inter, 9px, `#94A3B8` at 0.35
- Connection line: 1px, `#4A90D9` at 0.25, from callout to line

#### Annotation 2 — Uplevel Study
- Callout box: rounded rect, `#1A2332` fill, `#D9944A` 1px border at 0.3
- Position: right side of chart, pointing to the dashed amber line
- Text: "Overall throughput: ~0%" — Inter, 14px, bold, `#D9944A` at 0.8
- Subtext: "Uplevel, 2024 • 785 devs, one year" — Inter, 9px, `#94A3B8` at 0.35
- Second subtext line: "+41% more bugs" — Inter, 10px, `#E74C3C` at 0.6
- Connection line: 1px, `#D9944A` at 0.25

#### Annotation 3 — GitClear Data
- Callout box: rounded rect, `#1A2332` fill, `#E74C3C` 1px border at 0.3
- Position: below/right of debt shaded area
- Text line 1: "Code churn: +44%" — Inter, 13px, bold, `#E74C3C` at 0.75
- Text line 2: "Refactoring: −60%" — Inter, 13px, bold, `#E74C3C` at 0.75
- Subtext: "GitClear, 2025 • 211M lines analyzed" — Inter, 9px, `#94A3B8` at 0.35
- Connection line: 1px, `#E74C3C` at 0.25, pointing to shaded area

#### Debt Layer Decomposition
- Upper layer: "Code Complexity" — darker amber `#D9944A` at 0.10
- Lower layer: "Context Rot" — lighter amber `#D9944A` at 0.05 with animated noise/static texture at 0.03
- Dividing line: 1px dashed `#94A3B8` at 0.1 between layers
- Layer labels: Inter, 10px, `#94A3B8` at 0.35, left-aligned inside each layer

### Animation Sequence
1. **Frame 0-30 (0-1s):** Chart from previous spec holds. Brief pause.
2. **Frame 30-120 (1-4s):** Annotation 1 (GitHub −55%) fades in with a subtle 8px slide from right. Connection line draws.
3. **Frame 120-210 (4-7s):** Annotation 2 (Uplevel ~0%, +41% bugs) fades in below Annotation 1. The contrast between the two callouts is stark.
4. **Frame 210-240 (7-8s):** Brief hold. Let the viewer process the contradiction.
5. **Frame 240-360 (8-12s):** Annotation 3 (GitClear churn/refactoring) fades in near the debt area. Connection lines draw to the expanding shaded zone.
6. **Frame 360-540 (12-18s):** Hold for narration about code churn and piling on.
7. **Frame 540-660 (18-22s):** Debt area separates into two layers. "Code Complexity" label appears in upper layer. "Context Rot" label with static texture appears in lower layer.
8. **Frame 660-900 (22-30s):** Hold. Context Rot layer pulses with subtle noise animation, setting up transition to context window spec.

### Typography
- Annotation titles: Inter, 13-14px, bold, respective colors at 0.75-0.8
- Annotation subtext: Inter, 9-10px, `#94A3B8` at 0.35
- Bug count: Inter, 10px, `#E74C3C` at 0.6
- Layer labels: Inter, 10px, `#94A3B8` at 0.35

### Easing
- Annotation slide-in: `easeOut(cubic)` over 20 frames, 8px horizontal travel
- Connection line draw: `easeOut(quad)` over 15 frames
- Debt layer separation: `easeInOut(cubic)` over 30 frames
- Context Rot noise: `linear` continuous animation, opacity oscillates 0.02-0.04

## Narration Sync
> "GitHub measured a fifty-five percent speedup on individual coding tasks. But that was ninety-five developers writing one HTTP server from scratch. A greenfield task — exactly where AI shines."
> "When Uplevel tracked almost eight hundred developers across real enterprise work for a full year? No change in throughput. Forty-one percent more bugs."
> "And GitClear confirmed it across two hundred eleven million lines of code. Since AI coding assistants arrived, code churn is up forty-four percent... Meanwhile, refactoring collapsed by sixty percent. Developers aren't cleaning up. They're piling on."
> "But there's a second kind of debt hiding in there. One that's specific to AI-assisted development."

Segments: `part1_economics_013`, `part1_economics_014`, `part1_economics_015`, `part1_economics_016`

- **3:27** ("GitHub measured"): Annotation 1 appears
- **3:34** ("When Uplevel tracked"): Annotation 2 appears
- **3:42** ("GitClear confirmed"): Annotation 3 appears
- **3:50** ("a second kind of debt"): Debt area splits into two layers

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={900}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Chart base (continues from previous spec) */}
    <TripleLineChart data={chartData} />

    {/* Annotation 1: GitHub */}
    <Sequence from={30}>
      <SlideIn direction="right" distance={8} duration={20}>
        <FadeIn duration={20}>
          <AnnotationCallout
            title="Individual task: −55%"
            titleColor="#4A90D9"
            subtitle="GitHub, 2022 • 95 devs, one greenfield task"
            targetPoint={solidLineAt2022}
            borderColor="#4A90D9"
          />
        </FadeIn>
      </SlideIn>
    </Sequence>

    {/* Annotation 2: Uplevel */}
    <Sequence from={120}>
      <SlideIn direction="right" distance={8} duration={20}>
        <FadeIn duration={20}>
          <AnnotationCallout
            title="Overall throughput: ~0%"
            titleColor="#D9944A"
            subtitle="Uplevel, 2024 • 785 devs, one year"
            extra="+41% more bugs"
            extraColor="#E74C3C"
            targetPoint={dashedLineAt2024}
            borderColor="#D9944A"
          />
        </FadeIn>
      </SlideIn>
    </Sequence>

    {/* Annotation 3: GitClear */}
    <Sequence from={240}>
      <SlideIn direction="right" distance={8} duration={20}>
        <FadeIn duration={20}>
          <AnnotationCallout
            title={["Code churn: +44%", "Refactoring: −60%"]}
            titleColor="#E74C3C"
            subtitle="GitClear, 2025 • 211M lines analyzed"
            targetPoint={debtAreaCenter}
            borderColor="#E74C3C"
          />
        </FadeIn>
      </SlideIn>
    </Sequence>

    {/* Debt layer decomposition */}
    <Sequence from={540}>
      <DebtLayerSplit
        upperLabel="Code Complexity"
        lowerLabel="Context Rot"
        upperOpacity={0.10}
        lowerOpacity={0.05}
        noiseTexture={{ enabled: true, opacity: 0.03 }}
        splitDuration={30}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart_overlay",
  "chartType": "annotation_stack",
  "annotations": [
    {
      "id": "github_study",
      "title": "Individual task: −55%",
      "source": "GitHub, 2022",
      "detail": "95 developers, one greenfield task",
      "color": "#4A90D9",
      "targetSeries": "immediate_patch_cost",
      "targetX": 2022
    },
    {
      "id": "uplevel_study",
      "title": "Overall throughput: ~0%",
      "source": "Uplevel, 2024",
      "detail": "785 developers, one year",
      "extra": "+41% more bugs",
      "color": "#D9944A",
      "targetSeries": "total_cost_with_debt",
      "targetX": 2024
    },
    {
      "id": "gitclear_study",
      "title": ["Code churn: +44%", "Refactoring: −60%"],
      "source": "GitClear, 2025",
      "detail": "211M lines analyzed",
      "color": "#E74C3C",
      "targetArea": "debt_shaded_area"
    }
  ],
  "debtDecomposition": {
    "upperLayer": { "label": "Code Complexity", "color": "#D9944A", "opacity": 0.10 },
    "lowerLayer": { "label": "Context Rot", "color": "#D9944A", "opacity": 0.05, "noiseTexture": true }
  },
  "backgroundColor": "#0D1117",
  "narrationSegments": [
    "part1_economics_013", "part1_economics_014",
    "part1_economics_015", "part1_economics_016"
  ]
}
```

---
