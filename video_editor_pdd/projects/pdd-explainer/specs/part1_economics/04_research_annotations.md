[Remotion]

# Section 1.4: Research Study Annotations Overlay

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 3:10 - 3:28

## Visual Description
An annotation overlay that layers research study citations onto a simplified version of the cost chart from the previous component. Four study callouts materialize in sequence, each with a stat badge, citation, and fine print. The annotations create a building narrative: individual task speedup is real, but systemic throughput is flat, and code quality is degrading. Each annotation appears with a connecting leader line to the relevant part of the chart. The tone is "evidence stacking" — each study adds weight to the argument.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Inherited from previous chart (faint horizontal, `rgba(255,255,255,0.05)`)

### Chart/Visual Elements
- **Simplified Chart:** The triple-line chart from 03 is shown in a dimmed state (lines at 0.3 opacity) as background context, with the immediate patch line and debt area visible
- **Annotation 1 — GitHub Study:**
  - Position: Lower-left of chart, pointing to the dropping solid amber line
  - Stat Badge: "-55%" in `#22C55E` (green), 48px bold
  - Label: "Individual task speedup" — white, 18px
  - Citation: "GitHub, 2022" — muted `#94A3B8`, 14px
  - Fine Print: "95 developers, one greenfield task" — `#64748B`, 12px italic
  - Leader Line: 1px dashed `rgba(34,197,94,0.4)` connecting badge to the solid amber line
- **Annotation 2 — Uplevel Study:**
  - Position: Upper-right of chart, pointing to the flat dashed amber line
  - Stat Badge: "~0%" in `#EF4444` (red), 48px bold
  - Label: "Overall throughput" — white, 18px
  - Sub-stat: "+41% bugs" in `#EF4444`, 28px
  - Citation: "Uplevel, 2024" — muted `#94A3B8`, 14px
  - Fine Print: "785 developers, one year" — `#64748B`, 12px italic
  - Leader Line: 1px dashed `rgba(239,68,68,0.4)` connecting badge to dashed line
- **Annotation 3 — GitClear Study:**
  - Position: Center-right, pointing to the debt shaded area
  - Stat Badge: "+44%" in `#F59E0B` (amber-yellow), 48px bold
  - Label: "Code churn increase" — white, 18px
  - Sub-stat: "-60% refactoring" in `#EF4444`, 28px
  - Citation: "GitClear, 2025 — 211M lines analyzed" — muted `#94A3B8`, 14px
  - Leader Line: 1px dashed `rgba(245,158,11,0.4)` to the debt area
- **Annotation 4 — METR Study:**
  - Position: Lower-right, subtle — arrives last
  - Stat Badge: "-19%" in `#EF4444`, 36px bold
  - Label: "Experienced devs slower on mature repos" — white, 16px
  - Sub-stat: "Believed: +20% faster" — `#F59E0B`, 16px italic
  - Citation: "METR, 2025" — muted `#94A3B8`, 14px
  - Fine Print: "39-point perception gap" — `#64748B`, 12px

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Simplified chart fades in at 0.3 opacity as context layer
2. **Frame 30-120 (1.0-4.0s):** Annotation 1 (GitHub -55%) materializes — leader line draws, stat badge scales in (0→1.1→1.0), label and citation fade in. Solid amber line brightens momentarily to 0.8 opacity where leader connects
3. **Frame 120-240 (4.0-8.0s):** Annotation 2 (Uplevel ~0%, +41% bugs) materializes — same pattern. Dashed amber line brightens where leader connects. The contrast between -55% and ~0% is visually stark
4. **Frame 240-370 (8.0-12.33s):** Annotation 3 (GitClear +44%, -60%) materializes. Debt area brightens/pulses subtly. The picture worsens
5. **Frame 370-470 (12.33-15.67s):** Annotation 4 (METR -19%) materializes — smaller, more understated. The perception gap sub-stat fades in with a beat delay
6. **Frame 470-540 (15.67-18.0s):** Hold. All four annotations visible simultaneously. A subtle connecting theme line traces between all four badges, forming a visual chain of evidence

### Typography
- Stat Badges: Inter, 48px (36px for METR), bold (800)
- Stat Labels: Inter, 18px (16px for METR), semi-bold (600), `#FFFFFF`
- Sub-stats: Inter, 28px (16px for METR), bold (700)
- Citations: Inter, 14px, regular (400), `#94A3B8`
- Fine Print: Inter, 12px, italic (400), `#64748B`

### Easing
- Leader line draw: `easeOut(cubic)`
- Stat badge scale: `easeOut(back(1.3))`
- Label/citation fade: `easeOut(quad)`
- Chart line brighten: `easeInOut(quad)`
- Debt area pulse: `easeInOut(sine)`

## Narration Sync
> "GitHub measured a fifty-five percent speedup on individual coding tasks. But that was ninety-five developers writing one HTTP server from scratch. A greenfield task — exactly where AI shines."
> "When Uplevel tracked almost eight hundred developers across real enterprise work for a full year? No change in throughput. Forty-one percent more bugs."
> "And GitClear confirmed it across two hundred eleven million lines of code. Since AI coding assistants arrived, code churn is up forty-four percent. Meanwhile, refactoring collapsed by sixty percent."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  {/* Background chart context */}
  <Sequence from={0} durationInFrames={30}>
    <DimmedChart opacity={0.3} chartData={tripleLineData} />
  </Sequence>

  {/* GitHub Study */}
  <Sequence from={30} durationInFrames={90}>
    <StudyAnnotation
      stat="-55%"
      statColor="#22C55E"
      label="Individual task speedup"
      citation="GitHub, 2022"
      finePrint="95 developers, one greenfield task"
      position="bottom-left"
      leaderTarget="immediatePatchLine"
    />
  </Sequence>

  {/* Uplevel Study */}
  <Sequence from={120} durationInFrames={120}>
    <StudyAnnotation
      stat="~0%"
      statColor="#EF4444"
      subStat="+41% bugs"
      label="Overall throughput"
      citation="Uplevel, 2024"
      finePrint="785 developers, one year"
      position="top-right"
      leaderTarget="totalCostLine"
    />
  </Sequence>

  {/* GitClear Study */}
  <Sequence from={240} durationInFrames={130}>
    <StudyAnnotation
      stat="+44%"
      statColor="#F59E0B"
      subStat="-60% refactoring"
      label="Code churn increase"
      citation="GitClear, 2025 — 211M lines analyzed"
      position="center-right"
      leaderTarget="debtArea"
    />
  </Sequence>

  {/* METR Study */}
  <Sequence from={370} durationInFrames={100}>
    <StudyAnnotation
      stat="-19%"
      statColor="#EF4444"
      subStat="Believed: +20% faster"
      subStatColor="#F59E0B"
      label="Experienced devs slower on mature repos"
      citation="METR, 2025"
      finePrint="39-point perception gap"
      position="bottom-right"
      size="small"
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "studies": [
    {
      "id": "github",
      "stat": "-55%",
      "statColor": "#22C55E",
      "label": "Individual task speedup",
      "citation": "GitHub, 2022",
      "finePrint": "95 developers, one greenfield task",
      "position": "bottom-left"
    },
    {
      "id": "uplevel",
      "stat": "~0%",
      "statColor": "#EF4444",
      "subStat": "+41% bugs",
      "label": "Overall throughput",
      "citation": "Uplevel, 2024",
      "finePrint": "785 developers, one year",
      "position": "top-right"
    },
    {
      "id": "gitclear",
      "stat": "+44%",
      "statColor": "#F59E0B",
      "subStat": "-60% refactoring",
      "label": "Code churn increase",
      "citation": "GitClear, 2025",
      "finePrint": "211M lines analyzed",
      "position": "center-right"
    },
    {
      "id": "metr",
      "stat": "-19%",
      "statColor": "#EF4444",
      "subStat": "Believed: +20% faster",
      "subStatColor": "#F59E0B",
      "label": "Experienced devs slower on mature repos",
      "citation": "METR, 2025",
      "finePrint": "39-point perception gap",
      "position": "bottom-right"
    }
  ],
  "backgroundColor": "#0F172A"
}
```

---
