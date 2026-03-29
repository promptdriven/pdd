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
  AXES_SETTLE_END,
  X_MAX,
} from './constants';

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const axisOpacity = interpolate(frame, [0, AXES_SETTLE_END], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Generate horizontal grid lines
  const gridLines: number[] = [];
  for (let y = CHART_TOP + GRID_SPACING; y < CHART_BOTTOM; y += GRID_SPACING) {
    gridLines.push(y);
  }

  // X-axis tick labels (0, 2, 4, ... 20)
  const xTicks: number[] = [];
  for (let i = 0; i <= X_MAX; i += 2) {
    xTicks.push(i);
  }

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
            key={`grid-h-${y}`}
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
      </svg>

      {/* X-axis label */}
      <div
        style={{
          position: 'absolute',
          left: CHART_LEFT,
          top: CHART_BOTTOM + 50,
          width: CHART_WIDTH,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 400,
          color: AXIS_LABEL_COLOR,
          opacity: 0.6,
        }}
      >
        Time (maintenance cycles)
      </div>

      {/* Y-axis label */}
      <div
        style={{
          position: 'absolute',
          left: CHART_LEFT - 120,
          top: CHART_TOP + CHART_HEIGHT / 2,
          fontFamily: 'Inter, sans-serif',
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

      {/* X-axis tick labels */}
      {xTicks.map((tick) => {
        const xPos =
          CHART_LEFT + (tick / X_MAX) * CHART_WIDTH;
        return (
          <div
            key={`xtick-${tick}`}
            style={{
              position: 'absolute',
              left: xPos,
              top: CHART_BOTTOM + 10,
              transform: 'translateX(-50%)',
              fontFamily: 'Inter, sans-serif',
              fontSize: 14,
              fontWeight: 400,
              color: AXIS_LABEL_COLOR,
              opacity: 0.6,
            }}
          >
            {tick}
          </div>
        );
      })}
    </div>
  );
};
