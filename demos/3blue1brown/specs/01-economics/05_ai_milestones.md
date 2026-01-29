# Section 1.5: AI Milestones on the Falling Line

**Tool:** Remotion
**Duration:** ~18 seconds
**Timestamp:** 3:05 - 3:23

## Visual Description

Key AI model releases appear as markers on the "cost to generate" line. Each milestone pushes the line lower — but the drops are **not equal**. Early models cause small dips; the real plunge begins in mid-2024.

## Technical Specifications

### Canvas
- Continues from Section 1.4
- Focus shifts to the 2020-2025 region

### Chart Elements

Zoom in on the 2020-2025 section of the chart:
- The descent becomes more detailed
- Individual model releases marked
- **Drop sizes vary** to reflect actual capability gains (see benchmark data below)

### Milestone Markers

| Model | Date | Color | Icon | Drop Size | Evidence |
|-------|------|-------|------|-----------|---------|
| Codex / Copilot | 2021 | Blue | Circle | **Small** | Autocomplete only, ~43% accuracy on first try, local scope |
| GPT-4 | Mar 2023 | Purple | Circle | **Moderate** | ~80% HumanEval, but only ~4% SWE-bench (real-world bugs) |
| Claude 3.5 Sonnet | Jun 2024 | Orange | Circle | **Large** | 92% HumanEval, 49% SWE-bench Verified, #1 on Coding Arena |
| Claude 3.7 Sonnet | Feb 2025 | Orange | Circle | **Moderate** | 70.3% SWE-bench Verified, extended thinking |
| Frontier models | Late 2025 | Multi | Cluster | **Moderate** | 77-81% SWE-bench (Opus 4.5, GPT 5.2, Gemini 3) |

### Benchmark Sources

The drop sizes reflect measured capability progression:

**SWE-bench (real-world bug fixing, gold standard):**
- Oct 2023: ~4% (GPT-3.5, Claude 2 — barely functional)
- Apr 2024: ~12-18% (SWE-agent + GPT-4)
- Jun-Jul 2024: ~38-49% (Claude 3.5 Sonnet — the big jump)
- Late 2024: ~49-65% (Claude 3.5 Sonnet v2, o1)
- Feb 2025: ~70% (Claude 3.7 Sonnet)
- Late 2025: ~77-81% (Claude Opus 4.5, GPT 5.2, Gemini 3)

**HumanEval (function-level coding):**
- Codex (2021): ~27-37%
- GPT-4 (2023): ~80%
- GPT-4o (2024): 90.2%
- Claude 3.5 Sonnet (2024): 92%
- 2025 models: saturated (92%+)

**Chatbot Arena Coding Elo:**
- May 2023 – Mar 2024: GPT-4 dominant
- Mar 2024: Claude 3 Opus overtakes GPT-4
- Jun 2024: Claude 3.5 Sonnet ties #1 in coding Arena
- Late 2024: Claude 3.5 Sonnet (Oct) tops coding leaderboard
- Late 2025: Claude Opus 4.5 holds 1542 Elo, highest ever

### Animation Sequence

1. **Frame 0-60 (0-2s):** Zoom into 2020-2025 region
   - Rest of chart fades to 30% opacity
   - X-axis rescales
2. **Frame 60-150 (2-5s):** Codex/Copilot marker appears (2021)
   - Marker pops in with spring animation
   - Label: "Codex / Copilot"
   - Line drops a **small step** — autocomplete era
3. **Frame 150-240 (5-8s):** GPT-4 marker appears (Mar 2023)
   - Label: "GPT-4"
   - Line drops a **moderate step** — first capable model, but limited real-world impact
4. **Frame 240-330 (8-11s):** Claude 3.5 Sonnet marker appears (Jun 2024)
   - **Largest visual impact** — marker is slightly bigger, impact ring expands further
   - Label: "Claude 3.5 Sonnet"
   - Line drops a **dramatic step** — this is the inflection point
5. **Frame 330-390 (11-13s):** Claude 3.7 Sonnet marker appears (Feb 2025)
   - Label: "Claude 3.7 Sonnet"
   - Line drops another **moderate step**
6. **Frame 390-450 (13-15s):** Frontier cluster appears (Late 2025)
   - Three small markers appear in quick succession (staggered by 15 frames)
   - Labels: "Opus 4.5", "GPT 5.2", "Gemini 3"
   - Line settles at its lowest point
7. **Frame 450-540 (15-18s):** Hold, slight pulse on final position

### Visual Style

- Markers should feel like "events" that cause the line to drop
- Each appearance has a subtle "impact" effect — **scaled to match drop size**
- The Codex and GPT-4 drops should feel like incremental progress
- The Claude 3.5 Sonnet drop should feel like a **cliff** — the visual climax of this sequence
- The frontier cluster should feel like acceleration / convergence
- Labels appear next to markers, slightly staggered vertically to avoid overlap

### Typography

- Model names: Sans-serif, 16pt, white
- Year labels: 14pt, gray
- Optional: Small logos next to names (if available/legal)

### Easing

- Zoom: `easeInOutCubic`
- Marker pop-in: `spring({ damping: 12, stiffness: 200 })`
- Small drops: `easeOutQuad`, duration 20 frames
- Large drop (Claude 3.5 Sonnet): `easeOutQuad`, duration 40 frames — slower fall emphasizes magnitude

## Narration Sync

(Visual only during this section - the chart speaks for itself)

The narration from Section 1.4 continues:
> "...So when something broke, you patched. Of course you patched. It was rational."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={540}>
  {/* Zoom effect */}
  <Sequence from={0} durationInFrames={60}>
    <ZoomToRegion
      chart={<CodeCostChart />}
      region={{ startYear: 2020, endYear: 2026 }}
    />
  </Sequence>

  {/* Milestones — drop sizes vary */}
  <Sequence from={60}>
    <MilestoneMarker
      name="Codex / Copilot"
      year={2021}
      color="#3B82F6"
      dropSize="small"
    />
  </Sequence>

  <Sequence from={150}>
    <MilestoneMarker
      name="GPT-4"
      year={2023}
      color="#8B5CF6"
      dropSize="moderate"
    />
  </Sequence>

  <Sequence from={240}>
    <MilestoneMarker
      name="Claude 3.5 Sonnet"
      year={2024.5}
      color="#F59E0B"
      dropSize="large"
      impactScale={1.5}
    />
  </Sequence>

  <Sequence from={330}>
    <MilestoneMarker
      name="Claude 3.7 Sonnet"
      year={2025.15}
      color="#F59E0B"
      dropSize="moderate"
    />
  </Sequence>

  {/* Frontier cluster */}
  <Sequence from={390}>
    <MilestoneMarker name="Opus 4.5" year={2025.7} color="#F59E0B" dropSize="small" />
  </Sequence>
  <Sequence from={405}>
    <MilestoneMarker name="GPT 5.2" year={2025.8} color="#8B5CF6" dropSize="small" />
  </Sequence>
  <Sequence from={420}>
    <MilestoneMarker name="Gemini 3" year={2025.9} color="#EF4444" dropSize="small" />
  </Sequence>
</Sequence>
```

## Visual Style Notes

- This should feel like an **uneven staircase descent** — not equal steps
- Early drops (2021-2023) are incremental: autocomplete, then basic code generation
- The **mid-2024 drop is the cliff** — Claude 3.5 Sonnet changed what AI coding could actually do
- The late-2025 cluster shows competitive convergence — multiple companies reaching similar capability
- Clean, informative, data-driven — not promotional for any specific company

## Why These Milestones (Not Others)

**Removed from previous version:**
- **GPT-3 (2020):** Had no meaningful coding impact. Generated simple HTML snippets but was "not useful for programmers other than as an experiment."
- **Claude 1.0 (2023):** Limited release, not known for coding. Coding dominance came with 3.5 Sonnet in 2024.
- **Gemini 1.0 (2023):** Initial release had modest coding impact. Significant coding capability came later with 1.5 Pro and 2.0.

**Added:**
- **Claude 3.5 Sonnet (Jun 2024):** The SWE-bench score jumped from ~4% to ~49% in under a year. Topped Chatbot Arena coding leaderboard. First model developers preferred over GPT-4 for coding.
- **Claude 3.7 Sonnet (Feb 2025):** 70.3% SWE-bench Verified. Extended thinking enabled multi-step reasoning about code.
- **Frontier cluster (Late 2025):** Three competing models (Opus 4.5, GPT 5.2, Gemini 3) all reaching 77-81% SWE-bench, showing competitive convergence.

## Transition

Transition to context rot explanation (Section 1.6), then crossing point (Section 1.7).
