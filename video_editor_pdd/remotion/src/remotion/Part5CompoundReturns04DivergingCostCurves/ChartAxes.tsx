import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  FONT_FAMILY,
  X_MIN,
  X_MAX,
} from './constants';

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Axes fade in over first 30 frames
  const axisOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Generate horizontal grid lines
  const gridLines: number[] = [];
  for (let y = CHART_TOP; y <= CHART_BOTTOM; y += GRID_SPACING) {
    gridLines.push(y);
  }

  // X-axis tick positions
  const xTicks: number[] = [];
  for (let i = X_MIN; i <= X_MAX; i++) {
    xTicks.push(i);
  }

  const xToPixel = (x: number) =>
    CHART_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

  return (
    <div style={{ position: 'absolute', inset: 0, opacity: axisOpacity }}>
      {/* Horizontal grid lines */}
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {gridLines.map((y) => (
          <line
            key={`grid-${y}`}
            x1={CHART_LEFT}
            y1={y}
            x2={CHART_RIGHT}
            y2={y}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={GRID_OPACITY}
          />
        ))}

        {/* X-axis line */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_RIGHT}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={1.5}
        />

        {/* Y-axis line */}
        <line
          x1={CHART_LEFT}
          y1={CHART_TOP}
          x2={CHART_LEFT}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={1.5}
        />

        {/* X-axis tick marks and labels */}
        {xTicks.map((tick) => {
          const px = xToPixel(tick);
          return (
            <g key={`xtick-${tick}`}>
              <line
                x1={px}
                y1={CHART_BOTTOM}
                x2={px}
                y2={CHART_BOTTOM + 6}
                stroke={AXIS_COLOR}
                strokeWidth={1}
              />
              <text
                x={px}
                y={CHART_BOTTOM + 24}
                fill={AXIS_LABEL_COLOR}
                opacity={0.6}
                fontFamily={FONT_FAMILY}
                fontSize={14}
                fontWeight={400}
                textAnchor="middle"
              >
                {tick}
              </text>
            </g>
          );
        })}
      </svg>

      {/* X-axis label */}
      <div
        style={{
          position: 'absolute',
          left: CHART_LEFT,
          top: CHART_BOTTOM + 42,
          width: CHART_WIDTH,
          textAlign: 'center',
          fontFamily: FONT_FAMILY,
          fontSize: 14,
          fontWeight: 400,
          color: AXIS_LABEL_COLOR,
          opacity: 0.6,
        }}
      >
        Time (years)
      </div>

      {/* Y-axis label (rotated) */}
      <div
        style={{
          position: 'absolute',
          left: CHART_LEFT - 70,
          top: CHART_TOP + CHART_HEIGHT / 2,
          fontFamily: FONT_FAMILY,
          fontSize: 14,
          fontWeight: 400,
          color: AXIS_LABEL_COLOR,
          opacity: 0.6,
          transform: 'rotate(-90deg)',
          transformOrigin: 'center center',
          whiteSpace: 'nowrap',
        }}
      >
        Cumulative Cost
      </div>
    </div>
  );
};

export default ChartAxes;
