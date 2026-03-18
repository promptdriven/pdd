import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  xToPixel,
  yToPixel,
  AMBER_SOLID,
  SMALL_CODEBASE_DATA,
  LARGE_CODEBASE_DATA,
  PHASE_ARROW,
} from "./constants";

/**
 * Curved arrow from lower fork midpoint arcing up to upper fork midpoint.
 * Label: "Every patch adds code"
 */
export const CurvedArrow: React.FC = () => {
  const frame = useCurrentFrame();

  const drawStart = PHASE_ARROW.start;
  const drawDuration = 30;

  const progress = interpolate(
    frame,
    [drawStart, drawStart + drawDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const labelOpacity = interpolate(
    frame,
    [drawStart + drawDuration, drawStart + drawDuration + 15],
    [0, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < drawStart) return null;

  // Midpoints of each fork (around 2022.5)
  const lowerMidIdx = 2; // 2022
  const upperMidIdx = 2; // 2022
  const fromX = xToPixel(SMALL_CODEBASE_DATA[lowerMidIdx].x);
  const fromY = yToPixel(SMALL_CODEBASE_DATA[lowerMidIdx].y);
  const toX = xToPixel(LARGE_CODEBASE_DATA[upperMidIdx].x);
  const toY = yToPixel(LARGE_CODEBASE_DATA[upperMidIdx].y);

  // Control point for the curve — arc to the right
  const cpX = fromX + 120;
  const cpY = (fromY + toY) / 2;

  const pathD = `M ${fromX} ${fromY} Q ${cpX} ${cpY} ${toX} ${toY}`;

  // Approximate length for dash animation
  const approxLen = Math.sqrt((toX - fromX) ** 2 + (toY - fromY) ** 2) * 1.3;

  // Arrowhead at endpoint — compute tangent at end
  const t = 0.95;
  const tangentX = 2 * (1 - t) * (cpX - fromX) + 2 * t * (toX - cpX);
  const tangentY = 2 * (1 - t) * (cpY - fromY) + 2 * t * (toY - cpY);
  const angle = Math.atan2(tangentY, tangentX);
  const arrowSize = 8;

  const arrow1X = toX - arrowSize * Math.cos(angle - Math.PI / 6);
  const arrow1Y = toY - arrowSize * Math.sin(angle - Math.PI / 6);
  const arrow2X = toX - arrowSize * Math.cos(angle + Math.PI / 6);
  const arrow2Y = toY - arrowSize * Math.sin(angle + Math.PI / 6);

  // Label position — along the curve midpoint
  const labelX = cpX + 10;
  const labelY = cpY;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Curved arrow path */}
      <path
        d={pathD}
        fill="none"
        stroke={AMBER_SOLID}
        strokeWidth={2}
        strokeLinecap="round"
        opacity={0.3}
        strokeDasharray={approxLen}
        strokeDashoffset={approxLen * (1 - progress)}
      />

      {/* Arrowhead */}
      {progress > 0.9 && (
        <polygon
          points={`${toX},${toY} ${arrow1X},${arrow1Y} ${arrow2X},${arrow2Y}`}
          fill={AMBER_SOLID}
          opacity={0.3 * Math.min(1, (progress - 0.9) / 0.1)}
        />
      )}

      {/* Label */}
      <text
        x={labelX}
        y={labelY - 4}
        fill={AMBER_SOLID}
        fontSize={10}
        fontFamily="Inter, sans-serif"
        opacity={labelOpacity}
      >
        Every patch adds code
      </text>
    </svg>
  );
};

export default CurvedArrow;
