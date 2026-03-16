[Remotion]

# Section 1.3: Research Annotations — The Evidence Stack

**Tool:** Remotion
**Duration:** ~40s
**Timestamp:** 1:30 – 2:10

## Visual Description
Research citations appear as animated annotation cards that stack on screen, each delivering a data point that reinforces the argument. This is NOT a traditional chart — it's a dynamic evidence-stacking layout where each study appears as a floating card with key metrics highlighted. The cards build vertically, creating a visual "weight of evidence." Each card has a colored accent bar (green for positive-seeming results, red for concerning findings). By the end, the red cards dramatically outnumber the green, visually showing the balance of evidence.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F1923 (dark blue-black)
- No grid lines

### Chart/Visual Elements
- **Card layout:** Cards appear in a staggered vertical stack, centered on screen. Each card is 700×90px with rounded corners (8px radius), semi-transparent background (#1A2A3E at 90% opacity), and a 4px left accent bar.
- **Card 1 (Green accent #22C55E):**
  - Source: "GitHub, 2022"
  - Metric: "+55% speedup"
  - Detail: "95 developers · 1 greenfield HTTP server"
- **Card 2 (Red accent #EF4444):**
  - Source: "Uplevel, 2024"
  - Metric: "0% throughput · +41% bugs"
  - Detail: "785 developers · 1 year · real enterprise work"
- **Card 3 (Red accent #EF4444):**
  - Source: "GitClear, 2025"
  - Metric: "+44% churn · -60% refactoring"
  - Detail: "211M lines analyzed"
- **Card 4 (Red accent #EF4444):**
  - Source: "METR, 2025"
  - Metric: "-19% slower (experienced devs)"
  - Detail: "Brownfield repos · out-of-distribution tasks"
- **Card 5 (Orange accent #F59E0B):**
  - Source: "METR, 2025 (perception)"
  - Metric: "39-point perception gap"
  - Detail: "Believed +20% faster · Actually -19% slower"
- **Connecting theme text:** After all cards appear, centered below the stack: "Every study is correct. They measured different things."

### Animation Sequence
1. **Frame 0–30 (0–1s):** Background settles. A subtle header "The Research" fades in at top.
2. **Frame 30–120 (1–4s):** Card 1 slides in from right with spring physics. Green accent bar glows briefly. Synced with "GitHub measured a fifty-five percent speedup..."
3. **Frame 120–300 (4–10s):** Card 2 slides in below Card 1 from left. Red accent. Card 1 shifts up slightly to make room. Pause on the metrics — "+41% bugs" gets a brief text scale pulse. Synced with "When Uplevel tracked almost eight hundred developers..."
4. **Frame 300–480 (10–16s):** Card 3 appears below Card 2 from right. The "+44% churn" and "-60% refactoring" numbers animate (count up/down from 0). Synced with "And GitClear confirmed it..."
5. **Frame 480–660 (16–22s):** Card 4 slides in from left. The red tint on the stack is now dominant. Brief hold.
6. **Frame 660–840 (22–28s):** Card 5 appears with special treatment — the perception gap is shown as a split bar: green portion labeled "+20% (belief)" and red portion labeled "-19% (reality)" with a gap indicator showing "39 pts". Synced with "those same developers believed AI was making them twenty percent faster..."
7. **Frame 840–1020 (28–34s):** All cards are visible. They settle into final positions. The green Card 1 is visually outweighed by the four red/orange cards.
8. **Frame 1020–1200 (34–40s):** Theme text fades in below. Slow dissolve begins.

### Typography
- Header: Inter SemiBold, 24px, #8B9DC3
- Card source: Inter Medium, 14px, #8B9DC3
- Card metric: Inter Bold, 28px, #FFFFFF
- Card detail: Inter Regular, 12px, #6B7C93, italic
- Theme text: Inter SemiBold, 22px, #FFFFFF, opacity 0.9

### Easing
- Card slide-in: `spring({ damping: 15, stiffness: 120 })`
- Number count-up: `easeOutCubic`
- Metric pulse: `easeInOutSine` (scale 1.0 → 1.08 → 1.0, 400ms)
- Theme text fade: `easeOutQuad`

## Narration Sync
> "GitHub measured a fifty-five percent speedup on individual coding tasks. But that was ninety-five developers writing one HTTP server from scratch. A greenfield task — exactly where AI shines."

> "When Uplevel tracked almost eight hundred developers across real enterprise work for a full year? No change in throughput. Forty-one percent more bugs."

> "And GitClear confirmed it across two hundred eleven million lines of code. Since AI coding assistants arrived, code churn is up forty-four percent... refactoring collapsed by sixty percent. Developers aren't cleaning up. They're piling on."

Segments: `part1_economics_014` (89.28s – 103.20s), `part1_economics_015` (103.20s – 127.22s), `part1_economics_016` (128.04s – 149.92s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1200}>
  <AbsoluteFill style={{ backgroundColor: '#0F1923' }}>
    <Sequence from={0} durationInFrames={30}>
      <FadeIn><Header text="The Research" /></FadeIn>
    </Sequence>

    <Sequence from={30} durationInFrames={90}>
      <SlideInCard
        direction="right"
        accent="#22C55E"
        source="GitHub, 2022"
        metric="+55% speedup"
        detail="95 developers · 1 greenfield HTTP server"
        yOffset={0}
      />
    </Sequence>

    <Sequence from={120} durationInFrames={180}>
      <SlideInCard
        direction="left"
        accent="#EF4444"
        source="Uplevel, 2024"
        metric="0% throughput · +41% bugs"
        detail="785 developers · 1 year · real enterprise work"
        yOffset={1}
      />
    </Sequence>

    <Sequence from={300} durationInFrames={180}>
      <SlideInCard
        direction="right"
        accent="#EF4444"
        source="GitClear, 2025"
        metric="+44% churn · -60% refactoring"
        detail="211M lines analyzed"
        yOffset={2}
      />
    </Sequence>

    <Sequence from={480} durationInFrames={180}>
      <SlideInCard
        direction="left"
        accent="#EF4444"
        source="METR, 2025"
        metric="-19% slower (experienced devs)"
        detail="Brownfield repos · out-of-distribution tasks"
        yOffset={3}
      />
    </Sequence>

    <Sequence from={660} durationInFrames={180}>
      <PerceptionGapCard
        belief="+20%"
        reality="-19%"
        gap="39 pts"
        yOffset={4}
      />
    </Sequence>

    <Sequence from={1020} durationInFrames={180}>
      <FadeIn>
        <ThemeText text="Every study is correct. They measured different things." />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "studies": [
    {
      "source": "GitHub, 2022",
      "metric": "+55%",
      "type": "speedup",
      "sample": "95 developers",
      "context": "greenfield HTTP server",
      "sentiment": "positive"
    },
    {
      "source": "Uplevel, 2024",
      "throughputChange": "0%",
      "bugIncrease": "+41%",
      "sample": "785 developers",
      "duration": "1 year",
      "context": "real enterprise work",
      "sentiment": "negative"
    },
    {
      "source": "GitClear, 2025",
      "churnIncrease": "+44%",
      "refactoringDecline": "-60%",
      "linesAnalyzed": "211M",
      "sentiment": "negative"
    },
    {
      "source": "METR, 2025",
      "speedChange": "-19%",
      "context": "experienced devs, brownfield",
      "perceivedChange": "+20%",
      "perceptionGap": "39 points",
      "sentiment": "negative"
    }
  ]
}
```
