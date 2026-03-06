import React from "react";
import { useCurrentFrame, interpolate, Easing, spring } from "remotion";
import {
  CHART_LEFT,
  CHART_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  AXIS_COLOR,
  AXIS_TITLE_COLOR,
  GRID_COLOR,
  AMBER,
  GREEN,
  DANGER_RED,
  U_CURVE_POINTS,
  SWEET_SPOT_X,
  SWEET_SPOT_Y,
  X_MAX,
  Y_MAX,
  X_TICKS,
  Y_TICKS,
  CURVE_PATH_LENGTH,
} from "./constants";

// Convert data coordinates to SVG coordinates
function dataToSvg(dataX: number, dataY: number): { sx: number; sy: number } {
  const sx = CHART_LEFT + (dataX / X_MAX) * CHART_WIDTH;
  const sy = CHART_TOP + CHART_HEIGHT - (dataY / Y_MAX) * CHART_HEIGHT;
  return { sx, sy };
}

// Build a smooth cubic bezier path through the U-curve points (Catmull-Rom)
function buildCurvePath(): string {
  const svgPoints = U_CURVE_POINTS.map((p) => dataToSvg(p.x, p.y));
  if (svgPoints.length < 2) return "";

  let d = `M ${svgPoints[0].sx},${svgPoints[0].sy}`;

  for (let i = 0; i < svgPoints.length - 1; i++) {
    const p0 = svgPoints[Math.max(0, i - 1)];
    const p1 = svgPoints[i];
    const p2 = svgPoints[i + 1];
    const p3 = svgPoints[Math.min(svgPoints.length - 1, i + 2)];

    const tension = 0.3;
    const cp1x = p1.sx + (p2.sx - p0.sx) * tension;
    const cp1y = p1.sy + (p2.sy - p0.sy) * tension;
    const cp2x = p2.sx - (p3.sx - p1.sx) * tension;
    const cp2y = p2.sy - (p3.sy - p1.sy) * tension;

    d += ` C ${cp1x},${cp1y} ${cp2x},${cp2y} ${p2.sx},${p2.sy}`;
  }

  return d;
}

// Build closed area path for fill below curve
function buildAreaPath(): string {
  const curvePath = buildCurvePath();
  const lastPoint = dataToSvg(
    U_CURVE_POINTS[U_CURVE_POINTS.length - 1].x,
    U_CURVE_POINTS[U_CURVE_POINTS.length - 1].y,
  );
  const firstPoint = dataToSvg(U_CURVE_POINTS[0].x, U_CURVE_POINTS[0].y);
  const bottomY = CHART_TOP + CHART_HEIGHT;

  return `${curvePath} L ${lastPoint.sx},${bottomY} L ${firstPoint.sx},${bottomY} Z`;
}

interface UCurveChartProps {
  axesFadeStart: number;
  axesFadeEnd: number;
  curveDrawStart: number;
  curveDrawEnd: number;
  sweetSpotStart: number;
}

export const UCurveChart: React.FC<UCurveChartProps> = ({
  axesFadeStart,
  axesFadeEnd,
  curveDrawStart,
  curveDrawEnd,
  sweetSpotStart,
}) => {
  const frame = useCurrentFrame();

  const axesOpacity = interpolate(
    frame,
    [axesFadeStart, axesFadeEnd],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );

  const curveProgress = interpolate(
    frame,
    [curveDrawStart, curveDrawEnd],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const sweetSpotScale = spring({
    frame: frame - sweetSpotStart,
    fps: 30,
    config: { damping: 10, stiffness: 200 },
  });

  const sweetSpotVisible = frame >= sweetSpotStart;
  const sweetSpot = dataToSvg(SWEET_SPOT_X, SWEET_SPOT_Y);

  const curvePath = buildCurvePath();
  const areaPath = buildAreaPath();

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Horizontal grid lines */}
      {Y_TICKS.filter((v) => v > 0).map((val) => {
        const { sy } = dataToSvg(0, val);
        return (
          <line
            key={`hgrid-${val}`}
            x1={CHART_LEFT}
            y1={sy}
            x2={CHART_LEFT + CHART_WIDTH}
            y2={sy}
            stroke={GRID_COLOR}
            strokeWidth={1}
            strokeDasharray="6 4"
            opacity={axesOpacity * 0.3}
          />
        );
      })}

      {/* Y-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_TOP}
        x2={CHART_LEFT}
        y2={CHART_TOP + CHART_HEIGHT}
        stroke={AXIS_COLOR}
        strokeWidth={2}
        opacity={axesOpacity}
      />

      {/* X-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_TOP + CHART_HEIGHT}
        x2={CHART_LEFT + CHART_WIDTH}
        y2={CHART_TOP + CHART_HEIGHT}
        stroke={AXIS_COLOR}
        strokeWidth={2}
        opacity={axesOpacity}
      />

      {/* Y-axis tick labels */}
      {Y_TICKS.map((val) => {
        const { sy } = dataToSvg(0, val);
        const tickLabel = val === 0 ? "Low" : val >= 0.75 ? "High" : "";
        if (!tickLabel) return null;
        return (
          <text
            key={`ytick-${val}`}
            x={CHART_LEFT - 16}
            y={sy + 5}
            fill={AXIS_COLOR}
            fontSize={14}
            fontFamily="Inter, sans-serif"
            fontWeight={500}
            textAnchor="end"
            opacity={axesOpacity}
          >
            {tickLabel}
          </text>
        );
      })}

      {/* X-axis tick labels */}
      {X_TICKS.map((val) => {
        const { sx } = dataToSvg(val, 0);
        return (
          <g key={`xtick-${val}`} opacity={axesOpacity}>
            <line
              x1={sx}
              y1={CHART_TOP + CHART_HEIGHT}
              x2={sx}
              y2={CHART_TOP + CHART_HEIGHT + 6}
              stroke={AXIS_COLOR}
              strokeWidth={1.5}
            />
            <text
              x={sx}
              y={CHART_TOP + CHART_HEIGHT + 26}
              fill={AXIS_COLOR}
              fontSize={14}
              fontFamily="Inter, sans-serif"
              fontWeight={500}
              textAnchor="middle"
            >
              {val === 1000 ? "1000+" : val}
            </text>
          </g>
        );
      })}

      {/* X-axis title */}
      <text
        x={CHART_LEFT + CHART_WIDTH / 2}
        y={CHART_TOP + CHART_HEIGHT + 52}
        fill={AXIS_TITLE_COLOR}
        fontSize={16}
        fontFamily="Inter, sans-serif"
        fontWeight={500}
        textAnchor="middle"
        opacity={axesOpacity}
      >
        Module Size (lines)
      </text>

      {/* Y-axis title (rotated) */}
      <text
        x={CHART_LEFT - 55}
        y={CHART_TOP + CHART_HEIGHT / 2}
        fill={AXIS_TITLE_COLOR}
        fontSize={16}
        fontFamily="Inter, sans-serif"
        fontWeight={500}
        textAnchor="middle"
        transform={`rotate(-90, ${CHART_LEFT - 55}, ${CHART_TOP + CHART_HEIGHT / 2})`}
        opacity={axesOpacity}
      >
        Defect Rate
      </text>

      {/* Danger zone tints */}
      {curveProgress > 0 && (
        <>
          {/* Left danger zone — tiny modules */}
          <rect
            x={CHART_LEFT}
            y={CHART_TOP}
            width={CHART_WIDTH * 0.08}
            height={CHART_HEIGHT}
            fill={DANGER_RED}
            opacity={curveProgress * 0.06}
          />
          {/* Right danger zone — oversized modules */}
          <rect
            x={CHART_LEFT + CHART_WIDTH * 0.7}
            y={CHART_TOP}
            width={CHART_WIDTH * 0.3}
            height={CHART_HEIGHT}
            fill={DANGER_RED}
            opacity={curveProgress * 0.06}
          />
        </>
      )}

      {/* Area fill under curve */}
      {curveProgress > 0 && (
        <path d={areaPath} fill={AMBER} opacity={curveProgress * 0.1} />
      )}

      {/* U-curve line with draw animation */}
      {curveProgress > 0 && (
        <path
          d={curvePath}
          fill="none"
          stroke={AMBER}
          strokeWidth={3}
          strokeLinecap="round"
          strokeDasharray={CURVE_PATH_LENGTH}
          strokeDashoffset={CURVE_PATH_LENGTH * (1 - curveProgress)}
        />
      )}

      {/* Sweet spot marker */}
      {sweetSpotVisible && (
        <g>
          {/* Vertical dashed line from sweet spot down to x-axis */}
          <line
            x1={sweetSpot.sx}
            y1={sweetSpot.sy}
            x2={sweetSpot.sx}
            y2={CHART_TOP + CHART_HEIGHT}
            stroke={GREEN}
            strokeWidth={2}
            strokeDasharray="6 4"
            opacity={0.7 * sweetSpotScale}
          />

          {/* Green dot on curve */}
          <circle
            cx={sweetSpot.sx}
            cy={sweetSpot.sy}
            r={8 * sweetSpotScale}
            fill={GREEN}
          />
          <circle
            cx={sweetSpot.sx}
            cy={sweetSpot.sy}
            r={14 * sweetSpotScale}
            fill="none"
            stroke={GREEN}
            strokeWidth={2}
            opacity={0.5}
          />

          {/* "~250 lines" label */}
          <text
            x={sweetSpot.sx}
            y={sweetSpot.sy - 30}
            fill={GREEN}
            fontSize={22}
            fontFamily="Inter, sans-serif"
            fontWeight={700}
            textAnchor="middle"
            opacity={sweetSpotScale}
          >
            ~250 lines
          </text>

          {/* "Sweet spot" pill */}
          <rect
            x={sweetSpot.sx - 50}
            y={sweetSpot.sy - 62}
            width={100}
            height={24}
            rx={12}
            fill={`${GREEN}33`}
            stroke={GREEN}
            strokeWidth={1.5}
            opacity={sweetSpotScale}
          />
          <text
            x={sweetSpot.sx}
            y={sweetSpot.sy - 45}
            fill={GREEN}
            fontSize={13}
            fontFamily="Inter, sans-serif"
            fontWeight={600}
            textAnchor="middle"
            opacity={sweetSpotScale}
          >
            Sweet spot
          </text>
        </g>
      )}
    </svg>
  );
};

export default UCurveChart;
