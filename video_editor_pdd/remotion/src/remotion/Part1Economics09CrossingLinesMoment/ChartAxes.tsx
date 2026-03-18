import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MAX,
  AXIS_COLOR,
  GRID_COLOR,
  AI_MILESTONES,
  xToPixel,
  yToPixel,
  PHASE_CHART_IN,
} from "./constants";

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [PHASE_CHART_IN.start, PHASE_CHART_IN.end],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const yearLabels: number[] = [];
  for (let y = X_MIN; y <= X_MAX; y++) yearLabels.push(y);

  const hourTicks = [0, 5, 10, 15, 20];

  return (
    <div style={{ position: "absolute", inset: 0, opacity }}>
      <svg width={1920} height={1080} viewBox="0 0 1920 1080">
        {/* Grid lines */}
        {hourTicks.map((h) => {
          const py = yToPixel(h);
          return (
            <line
              key={`grid-h-${h}`}
              x1={CHART_LEFT}
              y1={py}
              x2={CHART_RIGHT}
              y2={py}
              stroke={GRID_COLOR}
              strokeWidth={1}
            />
          );
        })}

        {/* X axis */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_RIGHT}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={1}
          strokeOpacity={0.3}
        />

        {/* Y axis */}
        <line
          x1={CHART_LEFT}
          y1={CHART_TOP}
          x2={CHART_LEFT}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={1}
          strokeOpacity={0.3}
        />

        {/* Year labels */}
        {yearLabels.map((year) => (
          <text
            key={`year-${year}`}
            x={xToPixel(year)}
            y={CHART_BOTTOM + 30}
            fill={AXIS_COLOR}
            fontSize={11}
            fontFamily="Inter, sans-serif"
            textAnchor="middle"
            opacity={0.5}
          >
            {year}
          </text>
        ))}

        {/* Hour labels */}
        {hourTicks.map((h) => (
          <text
            key={`hour-${h}`}
            x={CHART_LEFT - 15}
            y={yToPixel(h) + 4}
            fill={AXIS_COLOR}
            fontSize={11}
            fontFamily="Inter, sans-serif"
            textAnchor="end"
            opacity={0.5}
          >
            {h}h
          </text>
        ))}

        {/* Y-axis title */}
        <text
          x={40}
          y={CHART_TOP + CHART_HEIGHT / 2}
          fill={AXIS_COLOR}
          fontSize={12}
          fontFamily="Inter, sans-serif"
          textAnchor="middle"
          opacity={0.4}
          transform={`rotate(-90, 40, ${CHART_TOP + CHART_HEIGHT / 2})`}
        >
          Developer Hours
        </text>

        {/* AI milestone markers — very dim */}
        {AI_MILESTONES.map((m) => {
          const mx = xToPixel(m.year);
          return (
            <g key={`ms-${m.year}`} opacity={0.06}>
              <line
                x1={mx}
                y1={CHART_TOP}
                x2={mx}
                y2={CHART_BOTTOM}
                stroke="#ffffff"
                strokeWidth={1}
                strokeDasharray="4 4"
              />
              <text
                x={mx}
                y={CHART_TOP - 8}
                fill="#ffffff"
                fontSize={9}
                fontFamily="Inter, sans-serif"
                textAnchor="middle"
              >
                {m.label}
              </text>
            </g>
          );
        })}
      </svg>
    </div>
  );
};

export default ChartAxes;
