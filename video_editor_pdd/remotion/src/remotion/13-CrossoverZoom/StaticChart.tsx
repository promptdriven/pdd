import React, { useMemo } from "react";
import { AbsoluteFill } from "remotion";
import {
  WIDTH,
  HEIGHT,
  CHART_X,
  CHART_Y,
  CHART_W,
  CHART_H,
  AXIS_COLOR,
  AXIS_TITLE_COLOR,
  GRID_COLOR,
  GRID_FRACTIONS,
  X_TICKS,
  PATCHING_POINTS,
  GENERATION_POINTS,
  TOTAL_COST_POINTS,
  PATCHING_COLOR_START,
  PATCHING_COLOR_END,
  GENERATION_COLOR_START,
  GENERATION_COLOR_END,
  TOTAL_COST_COLOR,
  PRIMARY_LINE_WIDTH,
  TOTAL_LINE_WIDTH,
  CROSSOVER_PX_X,
  CROSSOVER_PX_Y,
  CROSSOVER_DOT_COLOR,
  CROSSOVER_GLOW_COLOR,
} from "./constants";

interface Point {
  x: number;
  y: number;
}

function pointsToSmoothPath(points: Point[]): string {
  if (points.length < 2) return "";

  const scaled = points.map((p) => ({
    x: CHART_X + p.x * CHART_W,
    y: CHART_Y + CHART_H * (1 - p.y),
  }));

  let d = `M ${scaled[0].x} ${scaled[0].y}`;

  for (let i = 0; i < scaled.length - 1; i++) {
    const p0 = scaled[Math.max(0, i - 1)];
    const p1 = scaled[i];
    const p2 = scaled[i + 1];
    const p3 = scaled[Math.min(scaled.length - 1, i + 2)];

    const tension = 0.3;
    const cp1x = p1.x + (p2.x - p0.x) * tension;
    const cp1y = p1.y + (p2.y - p0.y) * tension;
    const cp2x = p2.x - (p3.x - p1.x) * tension;
    const cp2y = p2.y - (p3.y - p1.y) * tension;

    d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${p2.x} ${p2.y}`;
  }

  return d;
}

/**
 * A fully-drawn, static version of the cost crossover chart.
 * Rendered as if all animations have completed — lines, axes, labels, crossover dot all visible.
 * This is the "frozen" chart that gets zoomed into.
 */
export const StaticChart: React.FC = () => {
  const patchingPath = useMemo(
    () => pointsToSmoothPath(PATCHING_POINTS),
    [],
  );
  const generationPath = useMemo(
    () => pointsToSmoothPath(GENERATION_POINTS),
    [],
  );
  const totalCostPath = useMemo(
    () => pointsToSmoothPath(TOTAL_COST_POINTS),
    [],
  );

  // Line label positions (end of each line)
  const patchLast = PATCHING_POINTS[PATCHING_POINTS.length - 1];
  const genLast = GENERATION_POINTS[GENERATION_POINTS.length - 1];
  const totalLast = TOTAL_COST_POINTS[TOTAL_COST_POINTS.length - 1];

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <linearGradient
            id="zoomPatchingGrad"
            x1="0%"
            y1="0%"
            x2="100%"
            y2="0%"
          >
            <stop offset="0%" stopColor={PATCHING_COLOR_START} />
            <stop offset="100%" stopColor={PATCHING_COLOR_END} />
          </linearGradient>
          <linearGradient
            id="zoomGenerationGrad"
            x1="0%"
            y1="0%"
            x2="100%"
            y2="0%"
          >
            <stop offset="0%" stopColor={GENERATION_COLOR_START} />
            <stop offset="100%" stopColor={GENERATION_COLOR_END} />
          </linearGradient>
          <radialGradient id="zoomCrossoverGlow">
            <stop
              offset="0%"
              stopColor={CROSSOVER_GLOW_COLOR}
              stopOpacity={1}
            />
            <stop
              offset="100%"
              stopColor={CROSSOVER_GLOW_COLOR}
              stopOpacity={0}
            />
          </radialGradient>
        </defs>

        {/* Horizontal grid lines */}
        {GRID_FRACTIONS.map((frac) => {
          const y = CHART_Y + CHART_H * (1 - frac);
          return (
            <line
              key={`grid-${frac}`}
              x1={CHART_X}
              y1={y}
              x2={CHART_X + CHART_W}
              y2={y}
              stroke={GRID_COLOR}
              strokeWidth={1}
              strokeDasharray="6 4"
              opacity={0.15}
            />
          );
        })}

        {/* Y-axis */}
        <line
          x1={CHART_X}
          y1={CHART_Y}
          x2={CHART_X}
          y2={CHART_Y + CHART_H}
          stroke={AXIS_COLOR}
          strokeWidth={2}
        />

        {/* X-axis */}
        <line
          x1={CHART_X}
          y1={CHART_Y + CHART_H}
          x2={CHART_X + CHART_W}
          y2={CHART_Y + CHART_H}
          stroke={AXIS_COLOR}
          strokeWidth={2}
        />

        {/* X-axis tick marks */}
        {X_TICKS.map((t) => {
          const x = CHART_X + t * CHART_W;
          return (
            <line
              key={`xtick-${t}`}
              x1={x}
              y1={CHART_Y + CHART_H}
              x2={x}
              y2={CHART_Y + CHART_H + 8}
              stroke={AXIS_COLOR}
              strokeWidth={1.5}
            />
          );
        })}

        {/* Y-axis tick marks */}
        {GRID_FRACTIONS.map((frac) => {
          const y = CHART_Y + CHART_H * (1 - frac);
          return (
            <line
              key={`ytick-${frac}`}
              x1={CHART_X - 8}
              y1={y}
              x2={CHART_X}
              y2={y}
              stroke={AXIS_COLOR}
              strokeWidth={1.5}
            />
          );
        })}

        {/* X-axis endpoint labels */}
        <text
          x={CHART_X}
          y={CHART_Y + CHART_H + 36}
          fill={AXIS_COLOR}
          fontSize={18}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="start"
        >
          Small / New
        </text>
        <text
          x={CHART_X + CHART_W}
          y={CHART_Y + CHART_H + 36}
          fill={AXIS_COLOR}
          fontSize={18}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="end"
        >
          Large / Mature
        </text>

        {/* X-axis title */}
        <text
          x={CHART_X + CHART_W / 2}
          y={CHART_Y + CHART_H + 70}
          fill={AXIS_TITLE_COLOR}
          fontSize={20}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="middle"
        >
          Time / Codebase Size
        </text>

        {/* Y-axis title (rotated) */}
        <text
          x={CHART_X - 70}
          y={CHART_Y + CHART_H / 2}
          fill={AXIS_TITLE_COLOR}
          fontSize={20}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="middle"
          transform={`rotate(-90, ${CHART_X - 70}, ${CHART_Y + CHART_H / 2})`}
        >
          Cost per Change
        </text>

        {/* Y-axis $0 label */}
        <text
          x={CHART_X - 16}
          y={CHART_Y + CHART_H + 4}
          fill={AXIS_COLOR}
          fontSize={16}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="end"
        >
          $0
        </text>

        {/* Y-axis percentage markers */}
        {GRID_FRACTIONS.map((frac) => {
          const y = CHART_Y + CHART_H * (1 - frac);
          return (
            <text
              key={`ylabel-${frac}`}
              x={CHART_X - 16}
              y={y + 5}
              fill={AXIS_COLOR}
              fontSize={16}
              fontFamily="Inter, sans-serif"
              fontWeight={500}
              textAnchor="end"
            >
              {`${Math.round(frac * 100)}%`}
            </text>
          );
        })}

        {/* Line A: Patching cost */}
        <path
          d={patchingPath}
          fill="none"
          stroke="url(#zoomPatchingGrad)"
          strokeWidth={PRIMARY_LINE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
        />

        {/* Line B: Generation cost */}
        <path
          d={generationPath}
          fill="none"
          stroke="url(#zoomGenerationGrad)"
          strokeWidth={PRIMARY_LINE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
        />

        {/* Line C: Total cost (dashed) */}
        <path
          d={totalCostPath}
          fill="none"
          stroke={TOTAL_COST_COLOR}
          strokeWidth={TOTAL_LINE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray="8 6"
          opacity={0.6}
        />

        {/* Line labels */}
        <text
          x={CHART_X + patchLast.x * CHART_W + 12}
          y={CHART_Y + CHART_H * (1 - patchLast.y) + 6}
          fill={PATCHING_COLOR_START}
          fontSize={22}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
        >
          Cost of Patching
        </text>
        <text
          x={CHART_X + genLast.x * CHART_W + 12}
          y={CHART_Y + CHART_H * (1 - genLast.y) + 6}
          fill={GENERATION_COLOR_START}
          fontSize={22}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
        >
          Cost of Generation
        </text>
        <text
          x={CHART_X + totalLast.x * CHART_W + 12}
          y={CHART_Y + CHART_H * (1 - totalLast.y) + 6}
          fill={TOTAL_COST_COLOR}
          fontSize={22}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          opacity={0.6}
        >
          Total Cost
        </text>

        {/* Crossover glow ring */}
        <circle
          cx={CROSSOVER_PX_X}
          cy={CROSSOVER_PX_Y}
          r={30}
          fill="url(#zoomCrossoverGlow)"
          opacity={0.6}
        />

        {/* Crossover dot */}
        <circle
          cx={CROSSOVER_PX_X}
          cy={CROSSOVER_PX_Y}
          r={6}
          fill={CROSSOVER_DOT_COLOR}
        />
      </svg>
    </AbsoluteFill>
  );
};

export default StaticChart;
