# Section 5.6: Investment Comparison Table

**Tool:** Remotion
**Duration:** ~20 seconds
**Timestamp:** 19:10 - 19:30

## Visual Description

The compound curves graph dissolves into a clean investment comparison table that summarizes the argument. The table has three columns: "Investment", "Return (Patching)", and "Return (PDD)". Three rows animate in one by one: "Fix bug", "Improve code", "Document behavior". The patching column shows diminishing/local returns in amber, and the PDD column shows compounding/permanent returns in blue. This is the crystallization of the compound curves argument into a digestible format.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Table centered horizontally and vertically
- Graph from 5.1-5.5 fades out as the table fades in

### Animation Elements

1. **Graph-to-Table Transition**
   - The compound curves graph fades to 0% opacity over 1.5 seconds
   - The table fades in from 0% simultaneously
   - Optional: curves briefly morph into table border lines before settling

2. **Table Header Row**
   - Three columns: "Investment" | "Return (Patching)" | "Return (PDD)"
   - Header background: Slightly lighter dark (#252545)
   - Header text: White, bold, 26pt, sans-serif
   - "Return (Patching)" has a subtle amber (#D9944A) underline
   - "Return (PDD)" has a subtle blue (#4A90D9) underline
   - Column widths: 25% | 37.5% | 37.5%

3. **Row 1: Fix Bug**
   - Investment: "Fix bug"
   - Patching: "One place, once" -- amber tinted text (#D9944A at 80%)
   - PDD: "Impossible forever" -- blue tinted text (#4A90D9 at 80%)
   - Row background: Dark (#1E1E2E)

4. **Row 2: Improve Code**
   - Investment: "Improve code"
   - Patching: "One version" -- amber tinted text
   - PDD: "All future versions" -- blue tinted text
   - Row background: Alternating slightly lighter (#222242)

5. **Row 3: Document Behavior**
   - Investment: "Document behavior"
   - Patching: "One snapshot" -- amber tinted text
   - PDD: "Living specification" -- blue tinted text
   - Row background: Dark (#1E1E2E)

6. **Row Emphasis Effects**
   - As each row appears, the PDD column cell briefly glows with blue (#4A90D9) at 20% opacity
   - The patching column cells remain static (no glow -- diminishing returns, no energy)
   - After all rows are visible, a subtle pulse runs down the PDD column (compound effect)

7. **Table Border Styling**
   - Thin borders between cells: rgba(255, 255, 255, 0.15)
   - Outer border: rgba(255, 255, 255, 0.25)
   - Rounded corners on outer table: 8px border-radius
   - Clean, modern table aesthetic

### Visual Design

```
+----------------------------------------------+
|                                               |
|   +----------+------------------+------------+|
|   |Investment | Return(Patching)| Return(PDD)||
|   |----------+------------------+------------|+
|   |Fix bug   | One place, once  | Impossible ||
|   |          |                  | forever    ||
|   |----------+------------------+------------|+
|   |Improve   | One version      | All future ||
|   |code      |                  | versions   ||
|   |----------+------------------+------------|+
|   |Document  | One snapshot     | Living     ||
|   |behavior  |                  |specification|
|   +----------+------------------+------------+|
|                                               |
+----------------------------------------------+
```

### Animation Sequence

1. **Frame 0-45 (0-1.5s):** Graph dissolves, table structure appears
   - Compound curves graph fades out
   - Table outer border and header row fade in
   - Header text appears: "Investment", "Return (Patching)", "Return (PDD)"
   - Column underlines draw in (amber, blue)

2. **Frame 45-150 (1.5-5s):** Row 1 animates in
   - Row slides in from left (translateX: -30px -> 0, opacity: 0 -> 1)
   - "Fix bug" | "One place, once" | "Impossible forever"
   - PDD cell briefly glows blue
   - Brief pause for reading

3. **Frame 150-270 (5-9s):** Row 2 animates in
   - Same slide-in animation, staggered
   - "Improve code" | "One version" | "All future versions"
   - PDD cell briefly glows blue
   - Brief pause for reading

4. **Frame 270-390 (9-13s):** Row 3 animates in
   - Same slide-in animation, staggered
   - "Document behavior" | "One snapshot" | "Living specification"
   - PDD cell briefly glows blue
   - Brief pause for reading

5. **Frame 390-480 (13-16s):** Column-wide emphasis pulse
   - A blue pulse runs down the entire PDD column (top to bottom, 1 second)
   - The amber column remains static -- no pulse, no energy
   - Visual contrast: compound (alive, pulsing) vs. diminishing (static, fading)

6. **Frame 480-600 (16-20s):** Hold on complete table
   - All rows visible
   - Subtle ambient glow on PDD column
   - Clean hold for narration completion

### Code Structure (Remotion)

```typescript
const InvestmentTable: React.FC = () => {
  const frame = useCurrentFrame();

  // Graph fade out
  const graphOpacity = interpolate(
    frame, [0, 45], [1, 0],
    { extrapolateRight: 'clamp' }
  );

  // Table fade in
  const tableOpacity = interpolate(
    frame, [0, 45], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Row animations (slide + fade)
  const row1Progress = interpolate(frame, [45, 120], [0, 1], { extrapolateRight: 'clamp' });
  const row2Progress = interpolate(frame, [150, 225], [0, 1], { extrapolateRight: 'clamp' });
  const row3Progress = interpolate(frame, [270, 345], [0, 1], { extrapolateRight: 'clamp' });

  // PDD cell glow (brief pulse per row)
  const pddGlow1 = interpolate(frame, [90, 120, 150], [0, 1, 0], { extrapolateRight: 'clamp' });
  const pddGlow2 = interpolate(frame, [195, 225, 255], [0, 1, 0], { extrapolateRight: 'clamp' });
  const pddGlow3 = interpolate(frame, [315, 345, 375], [0, 1, 0], { extrapolateRight: 'clamp' });

  // Column-wide pulse
  const columnPulseProgress = interpolate(
    frame, [390, 450], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const rows = [
    {
      investment: 'Fix bug',
      patching: 'One place, once',
      pdd: 'Impossible forever',
      progress: row1Progress,
      glow: pddGlow1,
    },
    {
      investment: 'Improve code',
      patching: 'One version',
      pdd: 'All future versions',
      progress: row2Progress,
      glow: pddGlow2,
    },
    {
      investment: 'Document behavior',
      patching: 'One snapshot',
      pdd: 'Living specification',
      progress: row3Progress,
      glow: pddGlow3,
    },
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Fading graph from previous sections */}
      <div style={{ opacity: graphOpacity }}>
        <CompoundCurvesGraph />
      </div>

      {/* Investment table */}
      <div style={{
        opacity: tableOpacity,
        position: 'absolute',
        left: '50%',
        top: '50%',
        transform: 'translate(-50%, -50%)',
        width: 1200,
      }}>
        <table style={{
          width: '100%',
          borderCollapse: 'separate',
          borderSpacing: 0,
          borderRadius: 8,
          overflow: 'hidden',
          border: '1px solid rgba(255,255,255,0.25)',
        }}>
          <thead>
            <tr style={{ backgroundColor: '#252545' }}>
              <th style={headerStyle}>Investment</th>
              <th style={{
                ...headerStyle,
                borderBottom: '3px solid #D9944A',
              }}>Return (Patching)</th>
              <th style={{
                ...headerStyle,
                borderBottom: '3px solid #4A90D9',
              }}>Return (PDD)</th>
            </tr>
          </thead>
          <tbody>
            {rows.map((row, i) => (
              <TableRow
                key={i}
                {...row}
                rowIndex={i}
                columnPulseProgress={columnPulseProgress}
              />
            ))}
          </tbody>
        </table>
      </div>
    </AbsoluteFill>
  );
};

const TableRow: React.FC<{
  investment: string;
  patching: string;
  pdd: string;
  progress: number;
  glow: number;
  rowIndex: number;
  columnPulseProgress: number;
}> = ({ investment, patching, pdd, progress, glow, rowIndex, columnPulseProgress }) => {
  const slideX = interpolate(progress, [0, 1], [-30, 0]);
  const bgColor = rowIndex % 2 === 0 ? '#1E1E2E' : '#222242';

  return (
    <tr style={{
      opacity: progress,
      transform: `translateX(${slideX}px)`,
      backgroundColor: bgColor,
    }}>
      <td style={cellStyle}>{investment}</td>
      <td style={{ ...cellStyle, color: 'rgba(217, 148, 74, 0.8)' }}>
        {patching}
      </td>
      <td style={{
        ...cellStyle,
        color: 'rgba(74, 144, 217, 0.8)',
        backgroundColor: `rgba(74, 144, 217, ${glow * 0.2})`,
        boxShadow: columnPulseProgress > (rowIndex / 3)
          ? `inset 0 0 20px rgba(74, 144, 217, ${0.15 * (1 - Math.abs(columnPulseProgress - rowIndex / 3))})`
          : 'none',
      }}>
        {pdd}
      </td>
    </tr>
  );
};
```

### Typography

- Header: Bold, 26pt, sans-serif (system-ui)
- Cell text: Regular, 24pt, sans-serif
- PDD column text: Slightly bolder weight (600) for emphasis
- Investment column: White at 90% opacity
- Patching column: Amber (#D9944A) at 80% opacity
- PDD column: Blue (#4A90D9) at 80% opacity

### Easing

- Graph dissolve: `easeInQuad`
- Table fade-in: `easeOutCubic`
- Row slide-in: `easeOutCubic`
- PDD cell glow: `easeInOutQuad` (smooth pulse)
- Column pulse: `easeInOutQuad`

## Narration Sync

> "Every investment in the mold has compound returns. Every investment in patching has diminishing returns."

- "Every investment in the mold" -- the PDD column glows; the viewer's eye is drawn to "Impossible forever", "All future versions", "Living specification"
- "Every investment in patching" -- the amber column sits static; "One place, once", "One version", "One snapshot"
- "compound returns" / "diminishing returns" -- these words land as the column pulse runs down the PDD column, emphasizing the contrast

## Audio Notes

- Soft transition sound as graph dissolves to table
- Each row slide-in: subtle "click" or "snap" (clean, typographic feel)
- Blue glow pulses: brief harmonic tone per row
- Column-wide pulse: sustained, warm tone (arrival, resolution)
- Overall: clean, precise audio matching the typographic visual

## Visual Style Notes

- The table should feel like a clean, authoritative summary after the mathematical graph
- Typography is the star here -- precise, well-spaced, easy to read at a glance
- The amber/blue color coding connects directly to the curve colors from 5.1-5.5
- The PDD column glow is subtle but meaningful -- it suggests ongoing vitality (compound)
- The patching column's lack of animation is equally meaningful (diminishing, static)
- Row-by-row animation gives the viewer time to read and absorb each comparison

## Transition

Dissolves into Section 5.7 where we return to the grandmother/sock callback imagery.
