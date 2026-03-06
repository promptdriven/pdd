import React from "react";
import { AbsoluteFill } from "remotion";
import {
  CHART_X,
  CHART_Y,
  CHART_W,
  CHART_H,
  AXIS_COLOR,
  AXIS_TITLE_COLOR,
  GRID_COLOR,
  CROSSOVER_PX_X,
  CROSSOVER_PX_Y,
  PATCHING_POINTS,
  GENERATION_POINTS,
  TOTAL_COST_POINTS,
} from "./constants";

interface Point {
  x: number;
  y: number;
}

const GRID_FRACTIONS = [0.25, 0.5, 0.75];

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
 * Static chart at its fully-drawn final state.
 * Shows axes, grid, all three lines, line labels, and crossover dot.
 */
export const ChartSnapshot: React.FC = () => {
  const patchingPath = pointsToSmoothPath(PATCHING_POINTS);
  const generationPath = pointsToSmoothPath(GENERATION_POINTS);
  const totalPath = pointsToSmoothPath(TOTAL_COST_POINTS);

  // Label positions at line endpoints
  const patchEnd = PATCHING_POINTS[PATCHING_POINTS.length - 1];
  const genEnd = GENERATION_POINTS[GENERATION_POINTS.length - 1];
  const totalEnd = TOTAL_COST_POINTS[TOTAL_COST_POINTS.length - 1];

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <linearGradient id="zoomPatchGrad" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor="#EF4444" />
            <stop offset="100%" stopColor="#F59E0B" />
          </linearGradient>
          <linearGradient id="zoomGenGrad" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor="#3B82F6" />
            <stop offset="100%" stopColor="#22C55E" />
          </linearGradient>
        </defs>

        {/* Grid lines */}
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

        {/* Tick marks */}
        {[0, 0.2, 0.4, 0.6, 0.8, 1.0].map((t) => {
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

        {/* Axis labels */}
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

        {/* Patching cost line */}
        <path
          d={patchingPath}
          fill="none"
          stroke="url(#zoomPatchGrad)"
          strokeWidth={4}
          strokeLinecap="round"
          strokeLinejoin="round"
        />

        {/* Generation cost line */}
        <path
          d={generationPath}
          fill="none"
          stroke="url(#zoomGenGrad)"
          strokeWidth={4}
          strokeLinecap="round"
          strokeLinejoin="round"
        />

        {/* Total cost line (dashed) */}
        <path
          d={totalPath}
          fill="none"
          stroke="#94A3B8"
          strokeWidth={2}
          strokeLinecap="round"
          strokeDasharray="8 6"
          opacity={0.6}
        />

        {/* Line labels */}
        <text
          x={CHART_X + patchEnd.x * CHART_W + 12}
          y={CHART_Y + CHART_H * (1 - patchEnd.y) + 6}
          fill="#EF4444"
          fontSize={22}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
        >
          Cost of Patching
        </text>
        <text
          x={CHART_X + genEnd.x * CHART_W + 12}
          y={CHART_Y + CHART_H * (1 - genEnd.y) + 6}
          fill="#3B82F6"
          fontSize={22}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
        >
          Cost of Generation
        </text>
        <text
          x={CHART_X + totalEnd.x * CHART_W + 12}
          y={CHART_Y + CHART_H * (1 - totalEnd.y) + 6}
          fill="#94A3B8"
          fontSize={22}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
        >
          Total Cost
        </text>

        {/* Crossover dot */}
        <circle cx={CROSSOVER_PX_X} cy={CROSSOVER_PX_Y} r={6} fill="#FFFFFF" />
      </svg>
    </AbsoluteFill>
  );
};

export default ChartSnapshot;
