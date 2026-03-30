import React from 'react';
import {interpolate, useCurrentFrame, Easing} from 'remotion';

/**
 * BackgroundChart renders the underlying "code cost" chart that the annotations
 * overlay on top of. It includes:
 *   - Y axis with cost labels
 *   - X axis with year labels
 *   - Horizontal grid lines
 *   - Solid amber line (immediate patch cost – drops steeply)
 *   - Dashed amber line (total cost with debt – nearly flat)
 *   - A legend in the top-left area
 */

// ── Local constants (not re-exported) ──────────────────────────────
const CHART_LEFT = 160;
const CHART_RIGHT = 1760;
const CHART_TOP = 140;
const CHART_BOTTOM = 860;
const YEAR_START = 2019;
const YEAR_END = 2026;

const AMBER = '#F59E0B';
const GRID_COLOR = '#1E293B';
const AXIS_COLOR = '#64748B';

const SOLID_POINTS: [number, number][] = [
  [2019, 0.95],
  [2020, 0.90],
  [2021, 0.80],
  [2022, 0.65],
  [2023, 0.40],
  [2024, 0.28],
  [2025, 0.20],
  [2026, 0.15],
];

const DASHED_POINTS: [number, number][] = [
  [2019, 0.95],
  [2020, 0.93],
  [2021, 0.92],
  [2022, 0.90],
  [2023, 0.88],
  [2024, 0.87],
  [2025, 0.86],
  [2026, 0.85],
];

function yearToX(year: number): number {
  return interpolate(year, [YEAR_START, YEAR_END], [CHART_LEFT, CHART_RIGHT]);
}

function valueToY(value: number): number {
  return interpolate(value, [0, 1], [CHART_BOTTOM, CHART_TOP]);
}

function pointsToSvgPath(pts: [number, number][]): string {
  return pts
    .map(([year, val], i) => {
      const x = yearToX(year);
      const y = valueToY(val);
      return `${i === 0 ? 'M' : 'L'}${x},${y}`;
    })
    .join(' ');
}

function pathLength(pts: [number, number][]): number {
  let len = 0;
  for (let i = 1; i < pts.length; i++) {
    const dx = yearToX(pts[i][0]) - yearToX(pts[i - 1][0]);
    const dy = valueToY(pts[i][1]) - valueToY(pts[i - 1][1]);
    len += Math.sqrt(dx * dx + dy * dy);
  }
  return len;
}

const BackgroundChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Draw-on animation for the two lines (first 60 frames)
  const drawProgress = interpolate(frame, [0, 55], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const solidLen = pathLength(SOLID_POINTS);
  const dashedLen = pathLength(DASHED_POINTS);
  const solidOffset = solidLen * (1 - drawProgress);
  const dashedOffset = dashedLen * (1 - drawProgress);

  // Grid rows (0%, 25%, 50%, 75%, 100%)
  const gridValues = [0, 0.25, 0.5, 0.75, 1.0];

  // Year labels
  const years = [2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026];

  return (
    <div style={{position: 'absolute', inset: 0}}>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{position: 'absolute', top: 0, left: 0}}
      >
        {/* Horizontal grid lines */}
        {gridValues.map((v) => (
          <line
            key={v}
            x1={CHART_LEFT}
            y1={valueToY(v)}
            x2={CHART_RIGHT}
            y2={valueToY(v)}
            stroke={GRID_COLOR}
            strokeWidth={1}
          />
        ))}

        {/* Y-axis labels */}
        {gridValues.map((v) => (
          <text
            key={`label-${v}`}
            x={CHART_LEFT - 16}
            y={valueToY(v) + 5}
            textAnchor="end"
            fill={AXIS_COLOR}
            fontSize={13}
            fontFamily="Inter, sans-serif"
          >
            {`${Math.round(v * 100)}%`}
          </text>
        ))}

        {/* X-axis labels */}
        {years.map((yr) => (
          <text
            key={yr}
            x={yearToX(yr)}
            y={CHART_BOTTOM + 36}
            textAnchor="middle"
            fill={AXIS_COLOR}
            fontSize={13}
            fontFamily="Inter, sans-serif"
          >
            {yr}
          </text>
        ))}

        {/* Y axis title */}
        <text
          x={50}
          y={(CHART_TOP + CHART_BOTTOM) / 2}
          textAnchor="middle"
          fill={AXIS_COLOR}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          transform={`rotate(-90, 50, ${(CHART_TOP + CHART_BOTTOM) / 2})`}
        >
          Relative Cost
        </text>

        {/* Solid amber line — immediate patch cost */}
        <path
          d={pointsToSvgPath(SOLID_POINTS)}
          fill="none"
          stroke={AMBER}
          strokeWidth={2.5}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={solidLen}
          strokeDashoffset={solidOffset}
        />

        {/* Dashed amber line — total cost with debt */}
        <path
          d={pointsToSvgPath(DASHED_POINTS)}
          fill="none"
          stroke={AMBER}
          strokeWidth={2.5}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={`8 6`}
          style={{
            strokeDashoffset: dashedOffset,
            opacity: drawProgress,
          }}
        />
      </svg>

      {/* Legend */}
      <div
        style={{
          position: 'absolute',
          top: CHART_TOP - 10,
          left: CHART_LEFT + 40,
          display: 'flex',
          gap: 32,
          opacity: interpolate(frame, [20, 50], [0, 1], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }),
        }}
      >
        <div style={{display: 'flex', alignItems: 'center', gap: 8}}>
          <div
            style={{
              width: 28,
              height: 3,
              backgroundColor: AMBER,
              borderRadius: 2,
            }}
          />
          <span
            style={{
              color: '#CBD5E1',
              fontSize: 13,
              fontFamily: 'Inter, sans-serif',
            }}
          >
            Immediate patch cost
          </span>
        </div>
        <div style={{display: 'flex', alignItems: 'center', gap: 8}}>
          <div
            style={{
              width: 28,
              height: 0,
              borderTop: `3px dashed ${AMBER}`,
            }}
          />
          <span
            style={{
              color: '#CBD5E1',
              fontSize: 13,
              fontFamily: 'Inter, sans-serif',
            }}
          >
            Total cost (incl. debt)
          </span>
        </div>
      </div>

      {/* Chart title */}
      <div
        style={{
          position: 'absolute',
          top: 50,
          left: 0,
          width: 1920,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 26,
          fontWeight: 700,
          color: '#E2E8F0',
          opacity: interpolate(frame, [0, 30], [0, 1], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }),
        }}
      >
        Code Generation Cost vs. Long-Term Maintenance
      </div>
    </div>
  );
};

export default BackgroundChart;
