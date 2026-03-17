import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  CHART_X,
  CHART_Y,
  CHART_W,
  CHART_H,
  X_MIN,
  X_MAX,
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
  MILESTONE_OPACITY,
  MILESTONES,
  CHART_FADE_START,
  CHART_FADE_END,
  GENERATE_COST_DATA,
  PATCH_COST_DATA,
  TOTAL_COST_DATA,
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

/** Convert data points to a smooth cubic Bezier SVG path. */
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

/**
 * ChartBase: Renders axes, grid, milestones, and the three original lines
 * fully drawn (no animation — this component represents the chart
 * "returning" from a previous shot).
 */
export const ChartBase: React.FC = () => {
  const frame = useCurrentFrame();

  // Chart fades in quickly at the start
  const fadeIn = interpolate(frame, [CHART_FADE_START, CHART_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const generatePath = dataToSmoothPath(GENERATE_COST_DATA);
  const patchPath = dataToSmoothPath(PATCH_COST_DATA);
  const totalPath = dataToSmoothPath(TOTAL_COST_DATA);

  // Label positions (right end of each line)
  const genLast = GENERATE_COST_DATA[GENERATE_COST_DATA.length - 1];
  const patchLast = PATCH_COST_DATA[PATCH_COST_DATA.length - 1];
  const totalLast = TOTAL_COST_DATA[TOTAL_COST_DATA.length - 1];

  return (
    <AbsoluteFill style={{ opacity: fadeIn }}>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
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

        {/* Y-axis */}
        <line
          x1={CHART_X}
          y1={CHART_Y}
          x2={CHART_X}
          y2={CHART_Y + CHART_H}
          stroke={AXIS_COLOR}
          strokeWidth={1}
          opacity={0.25}
        />

        {/* X-axis */}
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
            <g key={`xtick-major-${year}`}>
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

        {/* Axis titles */}
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

        {/* AI milestone vertical markers (dimmed to 0.06) */}
        {MILESTONES.map((ms) => {
          const x = dataToPixelX(ms.year);
          return (
            <g key={`ms-${ms.year}`} opacity={MILESTONE_OPACITY}>
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
              >
                {ms.label}
              </text>
            </g>
          );
        })}

        {/* --- Original three lines (fully drawn, no animation) --- */}

        {/* Blue "generate" line — shown up to 2020 fork point only,
            the extended crossing version is rendered separately */}
        <defs>
          <filter id="glow-generate-base">
            <feGaussianBlur stdDeviation="6" />
          </filter>
        </defs>
        {/* Glow */}
        <path
          d={generatePath}
          fill="none"
          stroke={BLUE_LINE_COLOR}
          strokeWidth={BLUE_STROKE_WIDTH * 3}
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={0.2}
          filter="url(#glow-generate-base)"
        />
        {/* Main */}
        <path
          d={generatePath}
          fill="none"
          stroke={BLUE_LINE_COLOR}
          strokeWidth={BLUE_STROKE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
        {/* Label */}
        <text
          x={dataToPixelX(genLast.x) + 14}
          y={dataToPixelY(genLast.y) + 5}
          fill={BLUE_LINE_COLOR}
          fontSize={12}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          opacity={0.7}
        >
          Cost to generate
        </text>

        {/* Amber solid "immediate patch cost" line — drawn up to fork point */}
        <defs>
          <filter id="glow-patch-base">
            <feGaussianBlur stdDeviation="6" />
          </filter>
        </defs>
        <path
          d={patchPath}
          fill="none"
          stroke={AMBER_LINE_COLOR}
          strokeWidth={AMBER_SOLID_STROKE_WIDTH * 3}
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={0.2}
          filter="url(#glow-patch-base)"
        />
        <path
          d={patchPath}
          fill="none"
          stroke={AMBER_LINE_COLOR}
          strokeWidth={AMBER_SOLID_STROKE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
        <text
          x={dataToPixelX(patchLast.x) + 14}
          y={dataToPixelY(patchLast.y) + 5}
          fill={AMBER_LINE_COLOR}
          fontSize={12}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          opacity={0.7}
        >
          Immediate patch cost
        </text>

        {/* Amber dashed "total cost with debt" line */}
        <path
          d={totalPath}
          fill="none"
          stroke={AMBER_LINE_COLOR}
          strokeWidth={AMBER_DASHED_STROKE_WIDTH}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray="8 4"
          opacity={0.7}
        />
        <text
          x={dataToPixelX(totalLast.x) + 14}
          y={dataToPixelY(totalLast.y) + 5}
          fill={AMBER_LINE_COLOR}
          fontSize={12}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          opacity={0.5}
        >
          Total cost (with debt)
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default ChartBase;
