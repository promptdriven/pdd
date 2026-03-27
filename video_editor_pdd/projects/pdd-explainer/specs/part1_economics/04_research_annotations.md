[Remotion]

# Section 1.4: Research Annotations — GitHub vs. Uplevel Studies

**Tool:** Remotion
**Duration:** ~39s (1170 frames @ 30fps)
**Timestamp:** 1:42 - 2:21

## Visual Description

Overlay annotations appear on the existing code cost chart (spec 03). Two research study callouts materialize sequentially, creating a stark contrast between individual task speedup and overall throughput stagnation.

**First annotation** (pointing to the dropping solid amber line):
- "Individual task: −55% (GitHub, 2022)"
- Fine print: "95 developers, one greenfield task"

**Second annotation** (pointing to the nearly-flat dashed line):
- "Overall throughput: ~0% (Uplevel, 2024)"
- Fine print: "785 developers, one year"

The annotations are positioned to make the contrast visually undeniable — one points down (things getting faster), the other points flat (nothing actually changing). A subtle connecting line between them emphasizes the paradox.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (inherited from code cost chart)
- Chart elements from spec 03 remain visible

### Chart/Visual Elements

#### Annotation 1 — GitHub Study
- Position: Right side of chart, pointing to solid amber line near 2023
- Callout box: `#1E293B` fill, `#4A90D9` 1.5px border, 8px corner radius
- Main text: "Individual task: −55%" — Inter 18px, bold (700), `#4A90D9`
- Source: "(GitHub, 2022)" — Inter 14px, regular (400), `#94A3B8`
- Fine print: "95 developers, one greenfield task" — Inter 12px, italic, `#64748B` at 0.7
- Connector line: 1px `#4A90D9` at 0.5, from callout to solid amber line

#### Annotation 2 — Uplevel Study
- Position: Upper-right, pointing to dashed amber line
- Callout box: `#1E293B` fill, `#EF4444` 1.5px border, 8px corner radius
- Main text: "Overall throughput: ~0%" — Inter 18px, bold (700), `#EF4444`
- Source: "(Uplevel, 2024)" — Inter 14px, regular (400), `#94A3B8`
- Fine print: "785 developers, one year" — Inter 12px, italic, `#64748B` at 0.7
- Connector line: 1px `#EF4444` at 0.5, from callout to dashed amber line

#### Contrast Line
- Subtle dashed line connecting both annotation boxes, `#FFFFFF` at 0.08

### Animation Sequence
1. **Frame 0-60 (0-2s):** Chart from spec 03 holds. No new elements.
2. **Frame 60-150 (2-5s):** Annotation 1 materializes: connector line draws first, then callout box scales in, then text types.
3. **Frame 150-300 (5-10s):** Hold on first annotation. Narration covers the GitHub study details.
4. **Frame 300-390 (10-13s):** Annotation 2 materializes similarly, pointing to the dashed line.
5. **Frame 390-600 (13-20s):** Both visible. Contrast line draws between them. The visual paradox is clear.
6. **Frame 600-1170 (20-39s):** Hold. Both annotations visible as narration covers Uplevel quote and implications.

### Typography
- Annotation main: Inter, 18px, bold (700), respective accent colors
- Source label: Inter, 14px, regular (400), `#94A3B8`
- Fine print: Inter, 12px, italic, `#64748B` at 0.7

### Easing
- Connector line draw: `easeOut(quad)` over 30 frames
- Callout box: `easeOut(back)` with overshoot, over 20 frames
- Text type-in: `easeOut(quad)`, 2 frames per character
- Contrast line: `easeInOut(quad)` over 30 frames

## Narration Sync
> "GitHub measured a 55% speedup on individual coding tasks. But that was 95 developers writing one HTTP server from scratch. A greenfield task — exactly where AI shines."
> "When Uplevel tracked almost 800 developers across real enterprise work for a full year? No change in throughput. 41% more bugs."

Segments: `part1_economics_010`, `part1_economics_011`

- **102.06s** (seg 010): First annotation appears — "GitHub measured a 55% speedup"
- **115.06s** (seg 010 ends): First annotation fully visible
- **115.34s** (seg 011): Second annotation appears — "But people tracked almost 800 developers"
- **140.60s** (seg 011 ends): Both annotations visible, contrast clear

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1170}>
  {/* Underlying chart from spec 03 continues */}

  {/* Annotation 1: GitHub study */}
  <Sequence from={60}>
    <AnnotationCallout
      targetLine="immediate_patch" targetX={2023}
      borderColor="#4A90D9"
      mainText="Individual task: −55%"
      source="(GitHub, 2022)"
      finePrint="95 developers, one greenfield task"
      position={{ x: 1400, y: 520 }}
    />
  </Sequence>

  {/* Annotation 2: Uplevel study */}
  <Sequence from={300}>
    <AnnotationCallout
      targetLine="total_cost_debt" targetX={2024}
      borderColor="#EF4444"
      mainText="Overall throughput: ~0%"
      source="(Uplevel, 2024)"
      finePrint="785 developers, one year"
      position={{ x: 1400, y: 220 }}
    />
  </Sequence>

  {/* Contrast connector */}
  <Sequence from={390}>
    <DrawLine
      from={[1400, 480]} to={[1400, 260]}
      color="#FFFFFF" opacity={0.08}
      dashArray="4 4" drawDuration={30}
    />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "annotation_overlay",
  "chartRef": "code_cost_generate_vs_patch",
  "annotations": [
    {
      "id": "github_study",
      "mainText": "Individual task: −55%",
      "source": "GitHub, 2022",
      "finePrint": "95 developers, one greenfield task",
      "targetLine": "immediate_patch",
      "accentColor": "#4A90D9",
      "direction": "positive"
    },
    {
      "id": "uplevel_study",
      "mainText": "Overall throughput: ~0%",
      "source": "Uplevel, 2024",
      "finePrint": "785 developers, one year",
      "targetLine": "total_cost_debt",
      "accentColor": "#EF4444",
      "direction": "flat"
    }
  ],
  "narrationSegments": ["part1_economics_010", "part1_economics_011"]
}
```

---
