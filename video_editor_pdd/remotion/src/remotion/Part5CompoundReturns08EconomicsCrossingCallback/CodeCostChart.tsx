import React from "react";
import {
  CHART_LEFT,
  CHART_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_INTERVAL,
  GENERATE_COLOR,
  GENERATE_WIDTH,
  GENERATE_POINTS,
  PATCH_COLOR,
  PATCH_SOLID_WIDTH,
  PATCH_DASHED_WIDTH,
  PATCH_POINTS,
  DEBT_POINTS,
  DEBT_AREA_COLOR,
  DEBT_AREA_OPACITY,
  CHART_MIN_YEAR,
  CHART_MAX_YEAR,
  CHART_MIN_COST,
  CHART_MAX_COST,
  YEAR_LABELS,
  DATE_MARKER_COLOR,
  DATE_MARKER_OPACITY,
  LABEL_DIMMED_OPACITY,
} from "./constants";

// ── Helpers ────────────────────────────────────────────────────────────────
function toChartX(year: number): number {
  return (
    CHART_LEFT +
    ((year - CHART_MIN_YEAR) / (CHART_MAX_YEAR - CHART_MIN_YEAR)) * CHART_WIDTH
  );
}

function toChartY(cost: number): number {
  return (
    CHART_TOP +
    CHART_HEIGHT -
    ((cost - CHART_MIN_COST) / (CHART_MAX_COST - CHART_MIN_COST)) * CHART_HEIGHT
  );
}

function pointsToSvgPath(points: { x: number; y: number }[]): string {
  return points
    .map((p, i) => `${i === 0 ? "M" : "L"} ${toChartX(p.x).toFixed(1)} ${toChartY(p.y).toFixed(1)}`)
    .join(" ");
}

function pointsToAreaPath(
  topPoints: { x: number; y: number }[],
  bottomPoints: { x: number; y: number }[]
): string {
  const top = topPoints.map(
    (p, i) => `${i === 0 ? "M" : "L"} ${toChartX(p.x).toFixed(1)} ${toChartY(p.y).toFixed(1)}`
  );
  const bottom = [...bottomPoints]
    .reverse()
    .map((p) => `L ${toChartX(p.x).toFixed(1)} ${toChartY(p.y).toFixed(1)}`);
  return [...top, ...bottom, "Z"].join(" ");
}

// ── Crossing-point coordinates (exported for reuse) ─────────────────────
export const CROSSING_CX = toChartX(2025.6);
export const CROSSING_CY = (() => {
  // Interpolate the generate line at 2025.6
  const before = GENERATE_POINTS.find((p) => p.x === 2025.6);
  if (before) return toChartY(before.y);
  // Fallback: average of patch and generate at that year
  return toChartY(26);
})();

// ── Chart labels ────────────────────────────────────────────────────────────
const LEGEND_ITEMS = [
  { label: "Cost to generate", color: GENERATE_COLOR, dashed: false },
  { label: "Immediate patch", color: PATCH_COLOR, dashed: false },
  { label: "Total cost with debt", color: PATCH_COLOR, dashed: true },
];

interface CodeCostChartProps {
  dimOpacity?: number;
}

export const CodeCostChart: React.FC<CodeCostChartProps> = ({
  dimOpacity = LABEL_DIMMED_OPACITY,
}) => {
  // Build horizontal grid lines
  const gridLines: React.ReactNode[] = [];
  for (let y = CHART_TOP; y <= CHART_TOP + CHART_HEIGHT; y += GRID_INTERVAL) {
    gridLines.push(
      <line
        key={`grid-${y}`}
        x1={CHART_LEFT}
        y1={y}
        x2={CHART_LEFT + CHART_WIDTH}
        y2={y}
        stroke={GRID_COLOR}
        strokeOpacity={GRID_OPACITY}
        strokeWidth={1}
      />
    );
  }

  const debtAreaPath = pointsToAreaPath(DEBT_POINTS, PATCH_POINTS);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, width: "100%", height: "100%" }}
    >
      {/* Grid */}
      {gridLines}

      {/* Debt shaded area between amber lines */}
      <path
        d={debtAreaPath}
        fill={DEBT_AREA_COLOR}
        fillOpacity={DEBT_AREA_OPACITY}
      />

      {/* Total cost with debt line (amber dashed) */}
      <path
        d={pointsToSvgPath(DEBT_POINTS)}
        fill="none"
        stroke={PATCH_COLOR}
        strokeWidth={PATCH_DASHED_WIDTH}
        strokeDasharray="10 6"
        strokeOpacity={0.9}
      />

      {/* Immediate patch line (amber solid) */}
      <path
        d={pointsToSvgPath(PATCH_POINTS)}
        fill="none"
        stroke={PATCH_COLOR}
        strokeWidth={PATCH_SOLID_WIDTH}
      />

      {/* Generate line (blue) */}
      <path
        d={pointsToSvgPath(GENERATE_POINTS)}
        fill="none"
        stroke={GENERATE_COLOR}
        strokeWidth={GENERATE_WIDTH}
      />

      {/* Crossing dot */}
      <circle
        cx={CROSSING_CX}
        cy={CROSSING_CY}
        r={5}
        fill={GENERATE_COLOR}
        stroke="#FFFFFF"
        strokeWidth={2}
      />

      {/* Year labels (dimmed) */}
      {YEAR_LABELS.map((yr) => (
        <text
          key={yr}
          x={toChartX(yr)}
          y={CHART_TOP + CHART_HEIGHT + 30}
          fill={DATE_MARKER_COLOR}
          fillOpacity={DATE_MARKER_OPACITY}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          textAnchor="middle"
        >
          {yr}
        </text>
      ))}

      {/* Legend */}
      {LEGEND_ITEMS.map((item, i) => {
        const legendX = CHART_LEFT + 20;
        const legendY = CHART_TOP + 20 + i * 24;
        return (
          <g key={item.label} opacity={dimOpacity}>
            <line
              x1={legendX}
              y1={legendY}
              x2={legendX + 30}
              y2={legendY}
              stroke={item.color}
              strokeWidth={2.5}
              strokeDasharray={item.dashed ? "6 4" : "none"}
            />
            <text
              x={legendX + 38}
              y={legendY + 4}
              fill="#E2E8F0"
              fontSize={14}
              fontFamily="Inter, sans-serif"
            >
              {item.label}
            </text>
          </g>
        );
      })}
    </svg>
  );
};
