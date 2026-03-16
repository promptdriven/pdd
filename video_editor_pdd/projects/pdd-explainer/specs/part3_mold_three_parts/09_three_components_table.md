[Remotion]

# Section 3.8: Three Components — Hierarchy Table

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 15:16 – 15:36

## Visual Description
A structured table/diagram showing the three PDD components side by side with their hierarchy. Three columns — Prompt (blue), Tests (amber), Grounding (green) — each with a role label, description, and priority rank. Animated arrows show the override hierarchy: Tests > Prompt > Grounding. When conflicts arise, an animated scenario shows tests overriding a prompt directive and the prompt overriding a grounding style preference. The final frame reduces to a powerful closing statement: "The code is output. The mold is what matters." with the code representation fading to near-invisible while the three-part mold glows.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- Grid lines: None

### Chart/Visual Elements
- **Three component columns:** Centered horizontally, y: 160–600
  - Column 1 — Prompt: x=280, 340px wide
    - Header bar: `#4A90D9`, 6px top border
    - Icon: Document/page, `#4A90D9`
    - Title: "Prompt" — `#4A90D9`, 24px, bold
    - Role: "Intent" — `#FFFFFF` at 0.8, 16px
    - Description: "What you want and why" — `#94A3B8`, 14px
    - Priority: "2" in circle, `#4A90D9` border
  - Column 2 — Tests: x=680, 340px wide
    - Header bar: `#D9944A`, 6px top border
    - Icon: Shield/wall, `#D9944A`
    - Title: "Tests" — `#D9944A`, 24px, bold
    - Role: "Constraints" — `#FFFFFF` at 0.8, 16px
    - Description: "Boundaries code cannot cross" — `#94A3B8`, 14px
    - Priority: "1" in circle with crown/star accent, `#D9944A` border
  - Column 3 — Grounding: x=1080, 340px wide
    - Header bar: `#5AAA6E`, 6px top border
    - Icon: Gear/brush, `#5AAA6E`
    - Title: "Grounding" — `#5AAA6E`, 24px, bold
    - Role: "Style" — `#FFFFFF` at 0.8, 16px
    - Description: "How it looks and feels" — `#94A3B8`, 14px
    - Priority: "3" in circle, `#5AAA6E` border

- **Hierarchy arrows (y: 620–680):**
  - Arrow from Tests → Prompt: labeled "overrides", `#D9944A` at 0.5, 2px
  - Arrow from Prompt → Grounding: labeled "overrides", `#4A90D9` at 0.5, 2px
  - Summary: "Tests > Prompt > Grounding" — centered, `#FFFFFF` at 0.7, 18px

- **Conflict scenario (appears mid-sequence):**
  - Small animated vignette at y: 720–800
  - Scenario: Grounding says "use camelCase" (green tag), Prompt says "use descriptive names" (blue tag), Test says "function must return int" (amber tag)
  - Resolution: amber tag expands to full width, blue tag stays, green tag dims
  - Label: "When these conflict, tests win. Always." — `#FFFFFF` at 0.7, 16px

- **Closing statement (final phase):**
  - Three-part mold icon (from spec 02) glows at center
  - Code representation (gray text block) at right fades to 10% opacity
  - Text: "The code is output. The mold is what matters." — `#FFFFFF`, 28px, bold, centered at y=900
  - Subtle radial glow behind the mold icon, `rgba(255,255,255,0.05)`

### Animation Sequence
1. **Frame 0–60 (0–2.0s):** Three columns animate in left-to-right with 15-frame stagger. Each column: header bar draws left→right, icon scales up (0→1), title fades in, then role and description. Synced with "Prompt plus tests plus grounding. Intent plus constraints plus style."
2. **Frame 60–120 (2.0–4.0s):** Priority numbers appear in circles — "1" for Tests appears with a brief amber flash and crown accent. "2" for Prompt and "3" for Grounding follow. Tests column gets a subtle elevated shadow to emphasize primacy.
3. **Frame 120–210 (4.0–7.0s):** Hierarchy arrows draw between columns at the bottom. "overrides" labels type on. Summary text "Tests > Prompt > Grounding" fades in below. Synced with "Together, they form a complete specification."
4. **Frame 210–330 (7.0–11.0s):** Conflict scenario animates. Three colored tags appear in a row. Then resolution: amber (test) tag pulses and expands, blue (prompt) tag stays steady, green (grounding) tag dims to 30% opacity. "When these conflict, tests win. Always." types on below. Synced with "When these conflict, tests win. Always. The walls override the specification. The specification overrides the style."
5. **Frame 330–420 (11.0–14.0s):** Table columns compress/slide up to top 40% of screen. Below, a side-by-side appears: left is the three-part mold icon (from cross-section spec) glowing with all three colors. Right is a code block that starts at full opacity.
6. **Frame 420–510 (14.0–17.0s):** The code block fades from 100% → 10% opacity. Simultaneously, the mold icon glows brighter — amber walls pulse, blue cavity glows, green particles shimmer. The mold is what endures; the code is ephemeral.
7. **Frame 510–570 (17.0–19.0s):** Closing statement types on: "The code is output. The mold is what matters." Large, centered, definitive. Synced with "The code is output. The mold is what matters."
8. **Frame 570–600 (19.0–20.0s):** Hold. Mold icon maintains gentle tri-color glow. Statement at full opacity. Code block nearly invisible.

### Typography
- Column titles: Inter Bold, 24px, respective colors
- Role labels: Inter SemiBold, 16px, `#FFFFFF` at 0.8 opacity
- Descriptions: Inter Regular, 14px, `#94A3B8`
- Priority numbers: Inter Bold, 20px, respective colors, inside 36px circle
- Hierarchy summary: Inter SemiBold, 18px, `#FFFFFF` at 0.7 opacity
- "overrides" labels: Inter Regular, 13px, respective arrow colors at 0.5
- Conflict label: Inter Medium, 16px, `#FFFFFF` at 0.7 opacity
- Closing statement: Inter Bold, 28px, `#FFFFFF`

### Easing
- Column animation: `spring({ damping: 15, stiffness: 110 })` (staggered)
- Priority number pop: `spring({ damping: 10, stiffness: 150 })`
- Arrow draw: `easeOutQuad`
- Tag resolution: `easeInOutCubic`
- Code fade-out: `easeInOutCubic` (2s)
- Mold glow intensify: `easeInOutSine`
- Closing type-on: linear

## Narration Sync
> "Prompt plus tests plus grounding. Intent plus constraints plus style. Together, they form a complete specification."

> "When these conflict, tests win. Always. The walls override the specification. The specification overrides the style."

> "The code is output. The mold is what matters."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Three component columns */}
    <Sequence from={0} durationInFrames={60}>
      <ComponentColumn
        x={280}
        icon="document"
        title="Prompt"
        role="Intent"
        description="What you want and why"
        priority={2}
        color="#4A90D9"
        delay={0}
      />
      <ComponentColumn
        x={680}
        icon="shield"
        title="Tests"
        role="Constraints"
        description="Boundaries code cannot cross"
        priority={1}
        color="#D9944A"
        delay={15}
        crown={true}
      />
      <ComponentColumn
        x={1080}
        icon="gear"
        title="Grounding"
        role="Style"
        description="How it looks and feels"
        priority={3}
        color="#5AAA6E"
        delay={30}
      />
    </Sequence>

    {/* Priority numbers */}
    <Sequence from={60} durationInFrames={60}>
      <PriorityBadges priorities={[2, 1, 3]} colors={["#4A90D9", "#D9944A", "#5AAA6E"]} />
    </Sequence>

    {/* Hierarchy arrows */}
    <Sequence from={120} durationInFrames={90}>
      <HierarchyArrows
        links={[
          { from: "Tests", to: "Prompt", color: "#D9944A" },
          { from: "Prompt", to: "Grounding", color: "#4A90D9" },
        ]}
        summary="Tests > Prompt > Grounding"
      />
    </Sequence>

    {/* Conflict scenario */}
    <Sequence from={210} durationInFrames={120}>
      <ConflictResolution
        tags={[
          { text: "use camelCase", color: "#5AAA6E", outcome: "dim" },
          { text: "use descriptive names", color: "#4A90D9", outcome: "stay" },
          { text: "function must return int", color: "#D9944A", outcome: "expand" },
        ]}
        label="When these conflict, tests win. Always."
      />
    </Sequence>

    {/* Mold vs. Code comparison */}
    <Sequence from={330} durationInFrames={180}>
      <MoldVsCode
        moldGlowColors={["#D9944A", "#4A90D9", "#5AAA6E"]}
        codeFadeTarget={0.1}
      />
    </Sequence>

    {/* Closing statement */}
    <Sequence from={510} durationInFrames={60}>
      <TypeOnText
        text="The code is output. The mold is what matters."
        fontSize={28}
        fontWeight="bold"
        y={900}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "components": [
    {
      "name": "Prompt",
      "role": "Intent",
      "description": "What you want and why",
      "priority": 2,
      "color": "#4A90D9"
    },
    {
      "name": "Tests",
      "role": "Constraints",
      "description": "Boundaries code cannot cross",
      "priority": 1,
      "color": "#D9944A"
    },
    {
      "name": "Grounding",
      "role": "Style",
      "description": "How it looks and feels",
      "priority": 3,
      "color": "#5AAA6E"
    }
  ],
  "hierarchy": "Tests > Prompt > Grounding",
  "conflictRule": "When conflicts arise, tests win. Always.",
  "closingStatement": "The code is output. The mold is what matters."
}
```

---
