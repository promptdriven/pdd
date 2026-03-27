import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface ScaleArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  entranceFrame: number;
  drawDuration: number;
  arrowColor: string;
  arrowOpacity: number;
  label: string;
}

export const ScaleArrow: React.FC<ScaleArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  entranceFrame,
  drawDuration,
  arrowColor,
  arrowOpacity,
  label,
}) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - entranceFrame;

  if (relativeFrame < 0) return null;

  const drawProgress = interpolate(relativeFrame, [0, drawDuration], [0, 1], {
    easing: Easing.inOut(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Calculate midpoint for the curve
  const midX = (fromX + toX) / 2;
  const midY = Math.min(fromY, toY) - 30;

  // SVG path for curved arrow
  const path = `M ${fromX} ${fromY} Q ${midX} ${midY} ${toX} ${toY}`;

  // Calculate total path length approximation for dash animation
  const pathLength = 400;
  const dashOffset = pathLength * (1 - drawProgress);

  // Arrow head at the end point
  const arrowHeadOpacity = drawProgress > 0.8 ? (drawProgress - 0.8) / 0.2 : 0;

  // Label position at midpoint of curve
  const labelX = midX;
  const labelY = midY - 12;
  const labelOpacity = interpolate(relativeFrame, [drawDuration * 0.3, drawDuration * 0.8], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <svg
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        pointerEvents: "none",
      }}
    >
      {/* Curved arrow path */}
      <path
        d={path}
        stroke={arrowColor}
        strokeWidth={2}
        fill="none"
        opacity={arrowOpacity}
        strokeDasharray={pathLength}
        strokeDashoffset={dashOffset}
      />
      {/* Arrow head */}
      <polygon
        points={`${toX},${toY} ${toX - 8},${toY + 12} ${toX + 8},${toY + 12}`}
        fill={arrowColor}
        opacity={arrowOpacity * arrowHeadOpacity}
      />
      {/* Label */}
      <text
        x={labelX}
        y={labelY}
        textAnchor="middle"
        fontFamily="Inter, sans-serif"
        fontSize={12}
        fontWeight={400}
        fill={arrowColor}
        opacity={arrowOpacity * labelOpacity}
      >
        {label}
      </text>
    </svg>
  );
};

export default ScaleArrow;
