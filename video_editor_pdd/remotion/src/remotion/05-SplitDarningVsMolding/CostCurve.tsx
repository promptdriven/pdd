import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CURVE_WIDTH,
  CURVE_HEIGHT,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

interface CostCurveProps {
  type: "exponential" | "flat";
  color: string;
  drawStart: number;
  drawEnd: number;
  label: string;
}

export const CostCurve: React.FC<CostCurveProps> = ({
  type,
  color,
  drawStart,
  drawEnd,
  label,
}) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [drawStart, drawEnd],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const fadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Build the curve path
  const points = 50;
  const pathSegments: string[] = [];

  for (let i = 0; i <= points; i++) {
    const t = i / points;
    const x = t * CURVE_WIDTH;
    let y: number;

    if (type === "exponential") {
      // Exponential rise: y goes from bottom to top as cost increases
      const normalizedY = Math.pow(t, 2.5);
      y = CURVE_HEIGHT - normalizedY * CURVE_HEIGHT;
    } else {
      // Flat: constant low cost
      y = CURVE_HEIGHT * 0.75;
    }

    pathSegments.push(`${i === 0 ? "M" : "L"} ${x} ${y}`);
  }

  const pathD = pathSegments.join(" ");

  // Estimate total path length for stroke-dasharray animation
  const totalLength = type === "exponential" ? 420 : CURVE_WIDTH;
  const visibleLength = totalLength * drawProgress;

  return (
    <div
      style={{
        position: "relative",
        width: CURVE_WIDTH,
        height: CURVE_HEIGHT + 36,
        opacity: fadeOut,
      }}
    >
      <svg
        width={CURVE_WIDTH}
        height={CURVE_HEIGHT}
        viewBox={`0 0 ${CURVE_WIDTH} ${CURVE_HEIGHT}`}
      >
        {/* Faint axis lines */}
        <line
          x1={0}
          y1={CURVE_HEIGHT}
          x2={CURVE_WIDTH}
          y2={CURVE_HEIGHT}
          stroke="rgba(148, 163, 184, 0.2)"
          strokeWidth={1}
        />
        <line
          x1={0}
          y1={0}
          x2={0}
          y2={CURVE_HEIGHT}
          stroke="rgba(148, 163, 184, 0.2)"
          strokeWidth={1}
        />

        {/* The cost curve */}
        <path
          d={pathD}
          stroke={color}
          strokeWidth={3}
          fill="none"
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={totalLength}
          strokeDashoffset={totalLength - visibleLength}
        />
      </svg>

      {/* Curve label */}
      <div
        style={{
          marginTop: 10,
          fontFamily: "'Inter', sans-serif",
          fontWeight: 500,
          fontSize: 18,
          color: "#94A3B8",
          textAlign: "center",
          opacity: drawProgress,
        }}
      >
        {label}
      </div>
    </div>
  );
};

export default CostCurve;
