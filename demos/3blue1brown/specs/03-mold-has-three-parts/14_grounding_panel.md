# Section 3.14: Grounding Panel (Material Properties)

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 12:10 - 12:25

## Visual Description

A panel showing material properties appears. "Grounding" label. Different textures/colors flow: one labeled "OOP", one "Functional", one "Your Team's Style". This introduces the third type of capital: grounding that determines HOW the code is generated.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- New panel-focused layout

### Animation Elements

1. **Grounding Panel**
   - Green glow (#5AAA6E)
   - "GROUNDING CAPITAL" header
   - "The Material" subtitle

2. **Style Swatches**
   - Three distinct visual patterns
   - "OOP" - structured, class-like pattern
   - "Functional" - flowing, composition pattern
   - "Your Team's Style" - personalized pattern

3. **Material Properties Label**
   - Technical/scientific feel
   - Shows this is about HOW, not WHAT

4. **Section Title**
   - "Third: grounding"
   - Green-themed design

### Style Swatches

| Style | Visual Pattern | Color Tint |
|-------|----------------|------------|
| OOP | Grid/boxes (classes) | Blue-gray |
| Functional | Flowing lines (pipes) | Purple |
| Your Team's Style | Custom pattern | Green (#5AAA6E) |

### Animation Sequence

1. **Frame 0-90 (0-3s):** Panel entrance
   - Grounding panel slides in
   - Green glow establishes
   - "GROUNDING CAPITAL" header

2. **Frame 90-180 (3-6s):** OOP swatch
   - First style swatch appears
   - "OOP" label
   - Grid/box visual pattern

3. **Frame 180-270 (6-9s):** Functional swatch
   - Second style swatch appears
   - "Functional" label
   - Flowing/pipe visual pattern

4. **Frame 270-360 (9-12s):** Team style swatch
   - Third style swatch appears
   - "Your Team's Style" label
   - Personalized pattern
   - Green highlight (this is the focus)

5. **Frame 360-450 (12-15s):** Hold and explanation
   - All swatches visible
   - "Material Properties" label
   - Emphasis on customization

### Visual Design: Grounding Panel

```
┌─────────────────────────────────────────────────┐
│                                                 │
│           ╔══════════════════════╗              │
│           ║   GROUNDING CAPITAL  ║              │
│           ║     The Material     ║              │
│           ╚══════════════════════╝              │
│                                                 │
│    ┌──────────┐  ┌──────────┐  ┌──────────┐    │
│    │ ┌──┬──┐  │  │ ────────→│  │ ∼∼∼∼∼∼∼ │    │
│    │ │  │  │  │  │ ────────→│  │ ∼∼∼∼∼∼∼ │    │
│    │ ├──┼──┤  │  │ ────────→│  │ ∼∼∼∼∼∼∼ │    │
│    │ │  │  │  │  │ ────────→│  │ ∼∼∼∼∼∼∼ │    │
│    │ └──┴──┘  │  │          │  │         │    │
│    │          │  │          │  │  ◆      │    │
│    │   OOP    │  │Functional│  │Your Team│    │
│    │          │  │          │  │  Style  │    │
│    └──────────┘  └──────────┘  └──────────┘    │
│                                                 │
│    "Determines the properties of what fills    │
│     the mold"                                  │
│                                                 │
└─────────────────────────────────────────────────┘
```

### Code Structure (Remotion)

```typescript
const GroundingPanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel entrance
  const panelY = interpolate(
    frame,
    [0, 60],
    [100, 0],
    { extrapolateRight: 'clamp' }
  );

  const panelOpacity = interpolate(
    frame,
    [0, 60],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Swatch appearances
  const swatches = [
    { label: "OOP", pattern: "grid", start: 90 },
    { label: "Functional", pattern: "flow", start: 180 },
    { label: "Your Team's Style", pattern: "custom", start: 270 },
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Main panel */}
      <div style={{
        transform: `translateY(${panelY}px)`,
        opacity: panelOpacity,
      }}>
        {/* Header */}
        <GroundingHeader />

        {/* Style swatches */}
        <div style={{
          display: 'flex',
          justifyContent: 'center',
          gap: 40,
          marginTop: 60,
        }}>
          {swatches.map((swatch, i) => {
            const swatchOpacity = interpolate(
              frame,
              [swatch.start, swatch.start + 40],
              [0, 1],
              { extrapolateRight: 'clamp' }
            );
            return (
              <StyleSwatch
                key={i}
                label={swatch.label}
                pattern={swatch.pattern}
                opacity={swatchOpacity}
                isTeamStyle={swatch.label === "Your Team's Style"}
              />
            );
          })}
        </div>

        {/* Description */}
        <Description
          text="Determines the properties of what fills the mold"
          opacity={interpolate(frame, [360, 400], [0, 1])}
        />
      </div>
    </AbsoluteFill>
  );
};
```

### Style Swatch Component

```typescript
const StyleSwatch: React.FC<{
  label: string;
  pattern: 'grid' | 'flow' | 'custom';
  opacity: number;
  isTeamStyle: boolean;
}> = ({ label, pattern, opacity, isTeamStyle }) => {
  const borderColor = isTeamStyle ? '#5AAA6E' : '#444';
  const glowColor = isTeamStyle ? 'rgba(90, 170, 110, 0.3)' : 'none';

  return (
    <div style={{
      opacity,
      width: 180,
      height: 200,
      background: '#1E1E2E',
      border: `2px solid ${borderColor}`,
      borderRadius: 12,
      padding: 16,
      boxShadow: isTeamStyle ? `0 0 20px ${glowColor}` : 'none',
    }}>
      {/* Pattern visualization */}
      <PatternVisualization pattern={pattern} />

      {/* Label */}
      <div style={{
        marginTop: 16,
        textAlign: 'center',
        fontSize: 14,
        color: isTeamStyle ? '#5AAA6E' : '#888',
        fontWeight: isTeamStyle ? 'bold' : 'normal',
      }}>
        {label}
      </div>
    </div>
  );
};
```

### Pattern Visualizations

```typescript
const PatternVisualization: React.FC<{ pattern: string }> = ({ pattern }) => {
  switch (pattern) {
    case 'grid':
      // OOP: Grid of boxes representing classes
      return (
        <svg width="140" height="120">
          <rect x="10" y="10" width="55" height="45" stroke="#6688AA" fill="none" />
          <rect x="75" y="10" width="55" height="45" stroke="#6688AA" fill="none" />
          <rect x="10" y="65" width="55" height="45" stroke="#6688AA" fill="none" />
          <rect x="75" y="65" width="55" height="45" stroke="#6688AA" fill="none" />
          <line x1="65" y1="32" x2="75" y2="32" stroke="#6688AA" />
          <line x1="65" y1="87" x2="75" y2="87" stroke="#6688AA" />
        </svg>
      );

    case 'flow':
      // Functional: Flowing lines representing data flow
      return (
        <svg width="140" height="120">
          <path d="M10,30 Q70,10 130,30" stroke="#9966CC" fill="none" strokeWidth="2" />
          <path d="M10,60 Q70,40 130,60" stroke="#9966CC" fill="none" strokeWidth="2" />
          <path d="M10,90 Q70,70 130,90" stroke="#9966CC" fill="none" strokeWidth="2" />
          <circle cx="130" cy="30" r="4" fill="#9966CC" />
          <circle cx="130" cy="60" r="4" fill="#9966CC" />
          <circle cx="130" cy="90" r="4" fill="#9966CC" />
        </svg>
      );

    case 'custom':
      // Team style: Custom wavy pattern
      return (
        <svg width="140" height="120">
          <path d="M10,20 C30,10 50,30 70,20 S110,10 130,20" stroke="#5AAA6E" fill="none" strokeWidth="2" />
          <path d="M10,50 C30,40 50,60 70,50 S110,40 130,50" stroke="#5AAA6E" fill="none" strokeWidth="2" />
          <path d="M10,80 C30,70 50,90 70,80 S110,70 130,80" stroke="#5AAA6E" fill="none" strokeWidth="2" />
          <circle cx="70" cy="100" r="8" fill="#5AAA6E" opacity="0.5" />
        </svg>
      );
  }
};
```

### Easing

- Panel slide: `easeOutCubic`
- Swatch fade: `easeOutCubic`
- Team style glow: `easeInOutSine`

## Narration Sync

> "Third: grounding. This determines the properties of what fills the mold."

The panel appears as "Third: grounding" is spoken. Swatches appear sequentially during "properties of what fills the mold".

## Audio Notes

- Soft "slide" for panel entrance
- Subtle ping for each swatch
- Green-tinted audio for team style
- Different timbre from blue (prompt) and amber (tests)

## Visual Style Notes

- Green is the new accent color for grounding
- Three styles show variety is possible
- "Your Team's Style" is highlighted - this is personalized
- Material metaphor: same mold, different materials
- 3Blue1Brown: third color = third concept

## Transition

Continues into Section 3.15 showing OOP vs Functional code from same prompt.
