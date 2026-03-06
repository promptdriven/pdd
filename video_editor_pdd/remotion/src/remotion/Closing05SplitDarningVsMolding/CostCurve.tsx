import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CHART_LEFT,
  CHART_WIDTH,
  CHART_TOP,
  CHART_HEIGHT,
  CURVE_LABEL_FONT_SIZE,
  MUTED_TEXT_COLOR,
  DISSOLVE_START,
  DISSOLVE_END,
} from "./constants";

interface CostCurveProps {
  type: "exponential" | "flat";
  color: string;
  drawStart: number;
  drawEnd: number;
}

export const CostCurve: React.FC<CostCurveProps> = ({
  type,
  color,
  drawStart,
  drawEnd,
}) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [drawStart, drawEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  const fadeOut = interpolate(
    frame,
    [DISSOLVE_START, DISSOLVE_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );

  const label = type === "exponential" ? "Cost rises over time" : "Cost stays flat";

  // Generate path points
  const numPoints = 80;
  const points: string[] = [];

  for (let i = 0; i <= numPoints; i++) {
    const t = i / numPoints;
    const x = CHART_LEFT + t * CHART_WIDTH;
    let y: number;

    if (type === "exponential") {
      // Exponential rise: starts low-left, curves up sharply to upper-right
      const expVal = (Math.exp(t * 3) - 1) / (Math.exp(3) - 1);
      y = CHART_TOP + CHART_HEIGHT - expVal * CHART_HEIGHT;
    } else {
      // Flat line at ~75% of chart height from top (near bottom)
      y = CHART_TOP + CHART_HEIGHT * 0.75;
    }

    points.push(`${x},${y}`);
  }

  const pathD = `M ${points.join(" L ")}`;

  // SVG path length for dash animation
  const pathLength = 2000;

  return (
    <div style={{ position: "absolute", left: 0, top: 0, width: "100%", height: "100%", opacity: fadeOut }}>
      {/* Axis lines */}
      <svg
        width="100%"
        height="100%"
        style={{ position: "absolute", left: 0, top: 0 }}
      >
        {/* Y-axis */}
        <line
          x1={CHART_LEFT}
          y1={CHART_TOP}
          x2={CHART_LEFT}
          y2={CHART_TOP + CHART_HEIGHT}
          stroke="rgba(148, 163, 184, 0.3)"
          strokeWidth={1}
        />
        {/* X-axis */}
        <line
          x1={CHART_LEFT}
          y1={CHART_TOP + CHART_HEIGHT}
          x2={CHART_LEFT + CHART_WIDTH}
          y2={CHART_TOP + CHART_HEIGHT}
          stroke="rgba(148, 163, 184, 0.3)"
          strokeWidth={1}
        />
        {/* Cost curve path */}
        <path
          d={pathD}
          fill="none"
          stroke={color}
          strokeWidth={3}
          strokeLinecap="round"
          strokeDasharray={pathLength}
          strokeDashoffset={pathLength * (1 - drawProgress)}
        />
      </svg>

      {/* Curve label */}
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT,
          top: CHART_TOP + CHART_HEIGHT + 16,
          fontFamily: "Inter, sans-serif",
          fontWeight: 500,
          fontSize: CURVE_LABEL_FONT_SIZE,
          color: MUTED_TEXT_COLOR,
          opacity: drawProgress,
        }}
      >
        {label}
      </div>
    </div>
  );
};

export default CostCurve;
