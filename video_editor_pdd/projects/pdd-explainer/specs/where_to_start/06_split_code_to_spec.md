[split:]

# Section 6.6: Split Code to Spec — Before/After Comparison

**Tool:** Split
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 23:55 - 24:03

## Visual Description

A split-screen comparison shows the fundamental shift PDD creates. The LEFT half is labeled "Before: Code as Source" — it displays a dense `auth_module.py` file with ~200 lines of tightly-packed Python. Deprecation warnings, `# TODO` comments, and `# don't touch` annotations are visible in the code. It looks heavy, fragile, and intimidating. A line count badge reads "~200 lines."

The RIGHT half is labeled "After: Prompt as Source" — it shows a clean `auth_module.md` spec file (~20 lines of clear intent) paired with a compact `test_auth.py` (~10 lines). The spec is readable, the tests are focused. A line count badge reads "~20 lines + tests."

A golden "value" arrow animates from the left panel to the right, visualizing the migration of where value lives. The left side dims as the arrow lands, while the right side brightens — the code became the artifact, and the specification became the source of truth.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: none

### Chart/Visual Elements

#### Vertical Divider
- Position: x=960, from y=120 to y=960
- Color: `#334155` at 0.3
- Width: 2px

#### LEFT Panel — Code as Source
- Area: x 60-920, y 120-960
- Header: "Before: Code as Source" — Inter, 16px, semi-bold (600), `#94A3B8` at 0.6, left-aligned at (80, 150)

##### Code Block
- Position: (80, 190), 800w × 620h
- Background: `#0A0F1A`, rounded 8px, 1px `#1E293B` border
- File tab: "auth_module.py" — JetBrains Mono, 11px, `#94A3B8` at 0.5, with Python icon
- Code content: JetBrains Mono, 10px, `#94A3B8` at 0.35
  - Line numbers: `#334155` at 0.3, right-aligned gutter
  - Highlighted annotations:
    - `# don't touch` at line ~12: `#EF4444` at 0.5
    - `# TODO: fix later` at line ~47: `#FBBF24` at 0.4
    - `# DEPRECATED` at line ~83: `#EF4444` at 0.4
  - ~200 visible line numbers (densely packed, scroll impression)

##### Line Count Badge
- Position: bottom-right of code block, (830, 790)
- Background: `#D9944A` at 0.15, rounded 12px, 1px `#D9944A` at 0.3 border
- Text: "~200 lines" — Inter, 11px, semi-bold (600), `#D9944A`
- Padding: 4px 12px

#### RIGHT Panel — Prompt as Source
- Area: x 1000-1860, y 120-960
- Header: "After: Prompt as Source" — Inter, 16px, semi-bold (600), `#94A3B8` at 0.6, left-aligned at (1020, 150)

##### Spec Block
- Position: (1020, 190), 800w × 340h
- Background: `#0A0F1A`, rounded 8px, 1px `#4A90D9` at 0.2 border
- File tab: "auth_module.md" — JetBrains Mono, 11px, `#4A90D9` at 0.6, with document icon
- Spec content: Inter, 11px, `#E2E8F0` at 0.6
  - ~20 lines of clean specification text
  - Headings in `#4A90D9`: "## Purpose", "## Inputs", "## Behavior", "## Constraints"
  - Clean, readable prose — no code smells

##### Test Block
- Position: (1020, 560), 800w × 200h
- Background: `#0A0F1A`, rounded 8px, 1px `#5AAA6E` at 0.2 border
- File tab: "test_auth.py" — JetBrains Mono, 11px, `#5AAA6E` at 0.6, with test icon
- Test content: JetBrains Mono, 10px, `#5AAA6E` at 0.4
  - ~10 lines of focused test functions

##### Line Count Badge
- Position: bottom-right of test block, (1770, 740)
- Background: `#4A90D9` at 0.15, rounded 12px, 1px `#4A90D9` at 0.3 border
- Text: "~20 lines + tests" — Inter, 11px, semi-bold (600), `#4A90D9`
- Padding: 4px 12px

#### Value Arrow
- Shape: curved arrow from left panel center (490, 540) to right panel center (1430, 400)
- Color: `#FBBF24`, 3px stroke
- Arrowhead: 12px chevron
- Label: "value" — Inter, 12px, italic, `#FBBF24` at 0.6, positioned above arrow midpoint
- Glow trail: 6px Gaussian blur, `#FBBF24` at 0.1

### Animation Sequence
1. **Frame 0-30 (0-1s):** Divider line draws top-to-bottom. Both panel headers fade in.
2. **Frame 30-80 (1-2.67s):** LEFT code block fades in. Lines appear in a quick cascade (stagger 0.5 frames per line). Highlighted annotations (`# don't touch`, etc.) glow briefly red/amber. Line count badge pops in.
3. **Frame 80-140 (2.67-4.67s):** RIGHT spec block fades in — the clean, readable text appears. Then test block fades in below. Right line count badge pops in.
4. **Frame 140-190 (4.67-6.33s):** Golden value arrow draws from left to right, curving upward. "value" label fades in at midpoint. Arrow leaves a subtle glow trail.
5. **Frame 190-220 (6.33-7.33s):** LEFT panel dims to 0.3 opacity. RIGHT panel brightens — spec block border brightens to `#4A90D9` at 0.5, test block border brightens to `#5AAA6E` at 0.5.
6. **Frame 220-240 (7.33-8s):** Hold on final state. The contrast between dim left (artifact) and bright right (source of truth) is the takeaway.

### Typography
- Panel headers: Inter, 16px, semi-bold (600), `#94A3B8` at 0.6
- File tabs: JetBrains Mono, 11px, respective colors
- Code content: JetBrains Mono, 10px, `#94A3B8` at 0.35
- Spec content: Inter, 11px, `#E2E8F0` at 0.6
- Test content: JetBrains Mono, 10px, `#5AAA6E` at 0.4
- Badges: Inter, 11px, semi-bold (600), respective colors
- Arrow label: Inter, 12px, italic, `#FBBF24` at 0.6

### Easing
- Divider draw: `easeInOut(cubic)` over 25 frames
- Code cascade: linear stagger, 0.5 frames per line
- Annotation glow: `easeOut(quad)` pulse over 15 frames
- Badge pop: `easeOut(back(1.3))` over 12 frames
- Arrow draw: `easeInOut(cubic)` over 40 frames
- Left dim: `easeOut(quad)` opacity 1.0→0.3 over 20 frames
- Right brighten: `easeOut(quad)` border opacity increase over 20 frames

## Narration Sync
> "Just a gradual migration of where value lives, from code to specification."

Segment: `where_to_start_002`

- **23:55** ("Just a gradual migration"): Both panels visible, arrow begins drawing
- **23:57** ("of where value lives"): Arrow completes, "value" label visible
- **23:59** ("from code"): Left panel dims — code is now the artifact
- **24:01** ("to specification"): Right panel brightens — spec is the source of truth

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Vertical divider */}
    <Sequence from={0}>
      <LineDraw from={[960, 120]} to={[960, 960]}
        color="#334155" opacity={0.3} width={2} duration={25} />
    </Sequence>

    {/* Panel headers */}
    <Sequence from={5}>
      <FadeIn duration={15}>
        <Text text="Before: Code as Source" font="Inter" size={16}
          weight={600} color="#94A3B8" opacity={0.6}
          x={80} y={150} />
        <Text text="After: Prompt as Source" font="Inter" size={16}
          weight={600} color="#94A3B8" opacity={0.6}
          x={1020} y={150} />
      </FadeIn>
    </Sequence>

    {/* LEFT — Code block */}
    <Sequence from={30}>
      <CodeBlock x={80} y={190} width={800} height={620}
        filename="auth_module.py" language="python"
        lineCount={200} fontSize={10}
        highlights={[
          { line: 12, text: "# don't touch", color: '#EF4444' },
          { line: 47, text: '# TODO: fix later', color: '#FBBF24' },
          { line: 83, text: '# DEPRECATED', color: '#EF4444' }
        ]}
        cascadeStagger={0.5} />
      <Sequence from={40}>
        <BadgePop x={830} y={790} text="~200 lines"
          bgColor="#D9944A" textColor="#D9944A" />
      </Sequence>
    </Sequence>

    {/* RIGHT — Spec block */}
    <Sequence from={80}>
      <SpecBlock x={1020} y={190} width={800} height={340}
        filename="auth_module.md"
        headings={['Purpose','Inputs','Behavior','Constraints']}
        headingColor="#4A90D9" borderColor="#4A90D9" />
    </Sequence>

    {/* RIGHT — Test block */}
    <Sequence from={100}>
      <CodeBlock x={1020} y={560} width={800} height={200}
        filename="test_auth.py" language="python"
        lineCount={10} fontSize={10}
        borderColor="#5AAA6E" textColor="#5AAA6E" />
      <Sequence from={30}>
        <BadgePop x={1770} y={740} text="~20 lines + tests"
          bgColor="#4A90D9" textColor="#4A90D9" />
      </Sequence>
    </Sequence>

    {/* Value arrow */}
    <Sequence from={140}>
      <CurvedArrow from={[490, 540]} to={[1430, 400]}
        color="#FBBF24" width={3} arrowSize={12}
        drawDuration={40} glowBlur={6}
        label={{ text: 'value', font: 'Inter', size: 12,
          style: 'italic', color: '#FBBF24', opacity: 0.6 }} />
    </Sequence>

    {/* Dim left, brighten right */}
    <Sequence from={190}>
      <AnimateOpacity target="left_panel" to={0.3} duration={20} />
      <AnimateBorderBrightness targets={['spec_block','test_block']}
        to={0.5} duration={20} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_comparison",
  "comparisonId": "code_to_spec",
  "leftPanel": {
    "label": "Before: Code as Source",
    "file": "auth_module.py",
    "lineCount": 200,
    "annotations": ["don't touch", "TODO: fix later", "DEPRECATED"],
    "color": "#D9944A"
  },
  "rightPanel": {
    "label": "After: Prompt as Source",
    "files": [
      { "name": "auth_module.md", "lineCount": 20, "color": "#4A90D9" },
      { "name": "test_auth.py", "lineCount": 10, "color": "#5AAA6E" }
    ]
  },
  "valueArrow": { "color": "#FBBF24", "direction": "left_to_right" },
  "backgroundColor": "#0F172A",
  "narrationSegments": ["where_to_start_002"]
}
```

---
