/**
 * ChartBase — Renders the fully-drawn triple-line chart from spec 03.
 *
 * This component shows the chart in its final state (all lines drawn,
 * debt area filled) since this spec continues where 03 left off.
 */
import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame } from "remotion";
import {
  WIDTH,
  HEIGHT,
  CHART_X,
  CHART_Y,
  CHART_W,
  CHART_H,
  X_MIN,
  Y_MAX,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  GRID_COLOR,
  FONT_FAMILY,
  BLUE_LINE_COLOR,
  AMBER_LINE_COLOR,
  BLUE_STROKE_WIDTH,
  AMBER_SOLID_STROKE_WIDTH,
  AMBER_DASHED_STROKE_WIDTH,
  GENERATE_COST_DATA,
  PATCH_COST_DATA,
  TOTAL_COST_DATA,
  MILESTONES,
  DEBT_OPACITY_MIN,
  DEBT_OPACITY_MAX,
  DEBT_PULSE_CYCLE,
  DEBT_SPLIT_START,
  dataToPixelX,
  dataToPixelY,
} from "./constants";

interface DataPoint {
  x: number;
  y: number;
}

const Y_MAJOR_TICKS = [0, 5, 10, 15, 20];
const X_MAJOR_YEARS = [2015, 2017, 2019, 2021, 2023, 2025];
const X_MINOR_YEARS = [2016, 2018, 2020, 2022, 2024];

/** Convert data points to a smooth cubic Bézier SVG path. */
function dataToSmoothPath(data: DataPoint[]): string {
  if (data.length < 2) return "";
  const pts = data.map((d) => ({
    x: dataToPixelX(d.x),
    y: dataToPixelY(d.y),
  }));
  let d = `M ${pts[0].x} ${pts[0].y}`;
  const tension = 0.3;
  for (let i = 0; i < pts.length - 1; i++) {
    const p0 = pts[Math.max(0, i - 1)];
    const p1 = pts[i];
    const p2 = pts[i + 1];
    const p3 = pts[Math.min(pts.length - 1, i + 2)];
    const cp1x = p1.x + (p2.x - p0.x) * tension;
    const cp1y = p1.y + (p2.y - p0.y) * tension;
    const cp2x = p2.x - (p3.x - p1.x) * tension;
    const cp2y = p2.y - (p3.y - p1.y) * tension;
    d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${p2.x} ${p2.y}`;
  }
  return d;
}

/** Build polygon path for debt area between total cost and patch cost. */
function buildDebtAreaPath(): string {
  const upperPts = TOTAL_COST_DATA.map((d) => ({
    x: dataToPixelX(d.x),
    y: dataToPixelY(d.y),
  }));
  const lowerPts = PATCH_COST_DATA.map((d) => ({
    x: dataToPixelX(d.x),
    y: dataToPixelY(d.y),
  })).reverse();
  const all = [...upperPts, ...lowerPts];
  if (all.length === 0) return "";
  let d = `M ${all[0].x} ${all[0].y}`;
  for (let i = 1; i < all.length; i++) {
    d += ` L ${all[i].x} ${all[i].y}`;
  }
  d += " Z";
  return d;
}

export const ChartBase: React.FC = () => {
  const frame = useCurrentFrame();

  const bluePath = useMemo(() => dataToSmoothPath(GENERATE_COST_DATA), []);
  const amberSolidPath = useMemo(() => dataToSmoothPath(PATCH_COST_DATA), []);
  const amberDashedPath = useMemo(() => dataToSmoothPath(TOTAL_COST_DATA), []);
  const debtAreaPath = useMemo(() => buildDebtAreaPath(), []);

  // Debt area pulses
  const pulsePhase = frame / DEBT_PULSE_CYCLE;
  // Before split, show full debt area; after split, DebtLayerSplit takes over
  const showDebt = frame < DEBT_SPLIT_START;
  const debtOpacity = showDebt
    ? DEBT_OPACITY_MIN +
      (DEBT_OPACITY_MAX - DEBT_OPACITY_MIN) *
        (0.5 + 0.5 * Math.sin(pulsePhase * Math.PI * 2))
    : 0;

  // Line labels
  const labels = [
    {
      data: GENERATE_COST_DATA,
      color: BLUE_LINE_COLOR,
      text: "Cost to generate",
      opacity: 0.7,
    },
    {
      data: PATCH_COST_DATA,
      color: AMBER_LINE_COLOR,
      text: "Immediate patch cost",
      opacity: 0.7,
    },
    {
      data: TOTAL_COST_DATA,
      color: AMBER_LINE_COLOR,
      text: "Total cost (with debt)",
      opacity: 0.5,
    },
  ];

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <filter id="glow-blue">
            <feGaussianBlur stdDeviation="6" />
          </filter>
          <filter id="glow-amber">
            <feGaussianBlur stdDeviation="6" />
          </filter>
        </defs>

        {/* Horizontal grid lines */}
        {Y_MAJOR_TICKS.filter((v) => v > 0).map((val) => {
          const y = dataToPixelY(val);
          return (
            <line
              key={`grid-h-${val}`}
              x1={CHART_X}
              y1={y}
              x2={CHART_X + CHART_W}
              y2={y}
              stroke={GRID_COLOR}
              strokeWidth={1}
              strokeDasharray="6 4"
              opacity={0.08}
            />
          );
        })}

        {/* Y-axis line */}
        <line
          x1={CHART_X}
          y1={CHART_Y}
          x2={CHART_X}
          y2={CHART_Y + CHART_H}
          stroke={AXIS_COLOR}
          strokeWidth={1}
          opacity={0.25}
        />

        {/* X-axis line */}
        <line
          x1={CHART_X}
          y1={CHART_Y + CHART_H}
          x2={CHART_X + CHART_W}
          y2={CHART_Y + CHART_H}
          stroke={AXIS_COLOR}
          strokeWidth={1}
          opacity={0.25}
        />

        {/* X-axis major ticks and labels */}
        {X_MAJOR_YEARS.map((year) => {
          const x = dataToPixelX(year);
          return (
            <g key={`xtick-${year}`}>
              <line
                x1={x}
                y1={CHART_Y + CHART_H}
                x2={x}
                y2={CHART_Y + CHART_H + 8}
                stroke={AXIS_LABEL_COLOR}
                strokeWidth={1}
                opacity={0.25}
              />
              <text
                x={x}
                y={CHART_Y + CHART_H + 28}
                fill={AXIS_LABEL_COLOR}
                fontSize={10}
                fontFamily={FONT_FAMILY}
                fontWeight={400}
                textAnchor="middle"
                opacity={0.25}
              >
                {year}
              </text>
            </g>
          );
        })}

        {/* X-axis minor ticks */}
        {X_MINOR_YEARS.map((year) => {
          const x = dataToPixelX(year);
          return (
            <line
              key={`xtick-minor-${year}`}
              x1={x}
              y1={CHART_Y + CHART_H}
              x2={x}
              y2={CHART_Y + CHART_H + 5}
              stroke={AXIS_LABEL_COLOR}
              strokeWidth={1}
              opacity={0.15}
            />
          );
        })}

        {/* Y-axis ticks and labels */}
        {Y_MAJOR_TICKS.map((val) => {
          const y = dataToPixelY(val);
          return (
            <g key={`ytick-${val}`}>
              <line
                x1={CHART_X - 6}
                y1={y}
                x2={CHART_X}
                y2={y}
                stroke={AXIS_LABEL_COLOR}
                strokeWidth={1}
                opacity={0.25}
              />
              <text
                x={CHART_X - 14}
                y={y + 4}
                fill={AXIS_LABEL_COLOR}
                fontSize={10}
                fontFamily={FONT_FAMILY}
                fontWeight={400}
                textAnchor="end"
                opacity={0.25}
              >
                {val}
              </text>
            </g>
          );
        })}

        {/* X-axis title */}
        <text
          x={CHART_X + CHART_W / 2}
          y={CHART_Y + CHART_H + 56}
          fill={AXIS_LABEL_COLOR}
          fontSize={12}
          fontFamily={FONT_FAMILY}
          fontWeight={400}
          textAnchor="middle"
          opacity={0.3}
        >
          Year
        </text>

        {/* Y-axis title (rotated) */}
        <text
          x={CHART_X - 60}
          y={CHART_Y + CHART_H / 2}
          fill={AXIS_LABEL_COLOR}
          fontSize={12}
          fontFamily={FONT_FAMILY}
          fontWeight={400}
          textAnchor="middle"
          transform={`rotate(-90, ${CHART_X - 60}, ${CHART_Y + CHART_H / 2})`}
          opacity={0.3}
        >
          Cost (Developer Hours)
        </text>

        {/* AI milestone vertical markers */}
        {MILESTONES.map((ms) => {
          const x = dataToPixelX(ms.year);
          return (
            <g key={`ms-${ms.year}`} opacity={0.12}>
              <line
                x1={x}
                y1={CHART_Y}
                x2={x}
                y2={CHART_Y + CHART_H}
                stroke={AXIS_LABEL_COLOR}
                strokeWidth={1}
                strokeDasharray="4 3"
              />
              <text
                x={x}
                y={CHART_Y - 8}
                fill={AXIS_LABEL_COLOR}
                fontSize={9}
                fontFamily={FONT_FAMILY}
                fontWeight={400}
                textAnchor="end"
                transform={`rotate(-45, ${x}, ${CHART_Y - 8})`}
                opacity={0.3 / 0.12}
              >
                {ms.label}
              </text>
            </g>
          );
        })}

        {/* Debt shaded area (before split) */}
        {showDebt && (
          <path
            d={debtAreaPath}
            fill={AMBER_LINE_COLOR}
            opacity={debtOpacity}
          />
        )}

        {/* Blue line — Cost to generate (glow + main) */}
        <path
          d={bluePath}
          fill="none"
          stroke={BLUE_LINE_COLOR}
          strokeWidth={BLUE_STROKE_WIDTH * 3}
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={0.2}
          filter="url(#glow-blue)"
        />
        <path
          d={bluePath}
          fill="none"
          stroke={BLUE_LINE_COLOR}
          strokeWidth={BLUE_STROKE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
        />

        {/* Amber solid line — Immediate patch cost (glow + main) */}
        <path
          d={amberSolidPath}
          fill="none"
          stroke={AMBER_LINE_COLOR}
          strokeWidth={AMBER_SOLID_STROKE_WIDTH * 3}
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={0.2}
          filter="url(#glow-amber)"
        />
        <path
          d={amberSolidPath}
          fill="none"
          stroke={AMBER_LINE_COLOR}
          strokeWidth={AMBER_SOLID_STROKE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
        />

        {/* Amber dashed line — Total cost with debt */}
        <path
          d={amberDashedPath}
          fill="none"
          stroke={AMBER_LINE_COLOR}
          strokeWidth={AMBER_DASHED_STROKE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray="8 4"
        />

        {/* Line labels */}
        {labels.map((lbl) => {
          const last = lbl.data[lbl.data.length - 1];
          const lx = dataToPixelX(last.x) + 14;
          const ly = dataToPixelY(last.y) + 5;
          return (
            <text
              key={lbl.text}
              x={lx}
              y={ly}
              fill={lbl.color}
              fontSize={12}
              fontFamily={FONT_FAMILY}
              fontWeight={500}
              opacity={lbl.opacity}
            >
              {lbl.text}
            </text>
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};

export default ChartBase;
