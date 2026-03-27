import React from "react";
import { interpolate, Easing } from "remotion";
import {
  LINE_COLOR,
  CHART_LEFT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_PLOT_WIDTH,
  CHART_PLOT_HEIGHT,
  PERFORMANCE_DATA,
  INSET_WIDTH,
  INSET_HEIGHT,
  PHASE_LINE_DRAW_START,
} from "./constants";

interface AnimatedLineProps {
  localFrame: number;
}

/**
 * SVG animated declining line for the performance chart.
 * Draws from left to right over 120 frames starting at PHASE_LINE_DRAW_START.
 * Also renders a gradient fill under the line and animated data points.
 */
export const AnimatedLine: React.FC<AnimatedLineProps> = ({ localFrame }) => {
  // Line draw progress (90 → 210 frames, 120-frame duration)
  const drawProgress = interpolate(
    localFrame,
    [PHASE_LINE_DRAW_START, PHASE_LINE_DRAW_START + 120],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Convert data points to pixel coordinates
  const points = PERFORMANCE_DATA.map((dp) => ({
    px: CHART_LEFT + dp.x * CHART_PLOT_WIDTH,
    py: CHART_BOTTOM - dp.y * CHART_PLOT_HEIGHT,
    label: dp.label,
    value: dp.y,
  }));

  // Build SVG path
  const pathD = points
    .map((p, i) => `${i === 0 ? "M" : "L"} ${p.px} ${p.py}`)
    .join(" ");

  // Build area fill path (line + close to bottom)
  const areaD =
    pathD +
    ` L ${points[points.length - 1].px} ${CHART_BOTTOM}` +
    ` L ${points[0].px} ${CHART_BOTTOM} Z`;

  // Approximate total path length for dash animation
  let totalLength = 0;
  for (let i = 1; i < points.length; i++) {
    const dx = points[i].px - points[i - 1].px;
    const dy = points[i].py - points[i - 1].py;
    totalLength += Math.sqrt(dx * dx + dy * dy);
  }

  const gradientId = "line-gradient-fill";

  return (
    <svg
      width={INSET_WIDTH}
      height={INSET_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        <linearGradient id={gradientId} x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={LINE_COLOR} stopOpacity={0.25} />
          <stop offset="100%" stopColor={LINE_COLOR} stopOpacity={0.02} />
        </linearGradient>
        {/* Clip the area fill to the drawn portion */}
        <clipPath id="line-clip">
          <rect
            x={CHART_LEFT}
            y={CHART_TOP}
            width={CHART_PLOT_WIDTH * drawProgress}
            height={CHART_PLOT_HEIGHT + (CHART_BOTTOM - CHART_TOP - CHART_PLOT_HEIGHT) + 10}
          />
        </clipPath>
      </defs>

      {/* Gradient fill under line */}
      <path
        d={areaD}
        fill={`url(#${gradientId})`}
        clipPath="url(#line-clip)"
        opacity={drawProgress > 0 ? 0.6 : 0}
      />

      {/* Animated line */}
      <path
        d={pathD}
        fill="none"
        stroke={LINE_COLOR}
        strokeWidth={2.5}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalLength}
        strokeDashoffset={totalLength * (1 - drawProgress)}
      />

      {/* Data point dots */}
      {points.map((p, i) => {
        // Each point appears when the line reaches it
        const pointThreshold = i / (points.length - 1);
        const pointOpacity =
          drawProgress >= pointThreshold
            ? interpolate(
                drawProgress,
                [
                  Math.max(0, pointThreshold - 0.05),
                  Math.min(1, pointThreshold + 0.05),
                ],
                [0, 1],
                { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
              )
            : 0;

        return (
          <g key={p.label} opacity={pointOpacity}>
            {/* Outer glow */}
            <circle cx={p.px} cy={p.py} r={6} fill={LINE_COLOR} opacity={0.2} />
            {/* Inner dot */}
            <circle cx={p.px} cy={p.py} r={3} fill={LINE_COLOR} />
            {/* Value label */}
            <text
              x={p.px}
              y={p.py - 10}
              textAnchor="middle"
              fontFamily="Inter, sans-serif"
              fontSize={10}
              fill={LINE_COLOR}
              opacity={0.9}
            >
              {Math.round(p.value * 100)}%
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export default AnimatedLine;
