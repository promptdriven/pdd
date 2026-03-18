import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  AXIS_Y,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  TEXT_COLOR,
  AXES_START,
  AXES_DURATION,
  YEAR_LABELS,
} from './constants';

/**
 * X and Y axes with labels, animated draw-in.
 * Also renders the "Today" origin point.
 */
export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Progress for axis draw-in (0 → 1)
  const drawProgress = interpolate(
    frame,
    [AXES_START, AXES_START + AXES_DURATION],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const labelOpacity = interpolate(
    frame,
    [AXES_START + 10, AXES_START + AXES_DURATION],
    [0, 0.4],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // X-axis draws left to right
  const xEnd = CHART_LEFT + (CHART_RIGHT - CHART_LEFT) * drawProgress;
  // Y-axis draws bottom to top
  const yEnd = AXIS_Y - (AXIS_Y - CHART_TOP) * drawProgress;

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* X axis */}
      <line
        x1={CHART_LEFT}
        y1={AXIS_Y}
        x2={xEnd}
        y2={AXIS_Y}
        stroke={AXIS_COLOR}
        strokeWidth={2}
        opacity={0.4}
      />

      {/* Y axis */}
      <line
        x1={CHART_LEFT}
        y1={AXIS_Y}
        x2={CHART_LEFT}
        y2={yEnd}
        stroke={AXIS_COLOR}
        strokeWidth={2}
        opacity={0.4}
      />

      {/* X-axis year labels */}
      {YEAR_LABELS.map(({ x, label }) => (
        <text
          key={label}
          x={x}
          y={AXIS_Y + 28}
          textAnchor="middle"
          fill={AXIS_LABEL_COLOR}
          opacity={labelOpacity}
          fontFamily="Inter, sans-serif"
          fontSize={12}
          fontWeight={400}
        >
          {label}
        </text>
      ))}

      {/* Y-axis label (rotated) */}
      <text
        x={CHART_LEFT - 50}
        y={(CHART_TOP + AXIS_Y) / 2}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        opacity={labelOpacity}
        fontFamily="Inter, sans-serif"
        fontSize={12}
        fontWeight={400}
        transform={`rotate(-90, ${CHART_LEFT - 50}, ${(CHART_TOP + AXIS_Y) / 2})`}
      >
        Cumulative Cost
      </text>

      {/* Origin point */}
      <circle
        cx={CHART_LEFT}
        cy={780}
        r={6}
        fill={TEXT_COLOR}
        opacity={drawProgress * 0.6}
      />
      <text
        x={CHART_LEFT}
        y={780 + 22}
        textAnchor="middle"
        fill={TEXT_COLOR}
        opacity={drawProgress * 0.4}
        fontFamily="Inter, sans-serif"
        fontSize={11}
        fontWeight={400}
      >
        Today
      </text>
    </svg>
  );
};
