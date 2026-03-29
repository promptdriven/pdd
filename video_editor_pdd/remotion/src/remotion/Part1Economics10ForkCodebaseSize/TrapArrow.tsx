import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  ARROW_COLOR,
  ARROW_DRAW_START,
  ARROW_DRAW_END,
  ARROW_LABEL_START,
  SMALL_CODEBASE_DATA,
  LARGE_CODEBASE_DATA,
  mapX,
  mapY,
} from "./constants";

/**
 * Curved dashed arrow from the small codebase line sweeping up to the large codebase line.
 * Visualizes: "Every patch adds code" — the trap.
 */
export const TrapArrow: React.FC = () => {
  const frame = useCurrentFrame();

  // Arrow draw progress
  const drawProgress = interpolate(
    frame,
    [ARROW_DRAW_START, ARROW_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Arrow label opacity
  const labelOpacity = interpolate(
    frame,
    [ARROW_LABEL_START, ARROW_LABEL_START + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (frame < ARROW_DRAW_START) return null;

  // Arrow start: near end of small codebase line (around 2025)
  const arrowStartX = mapX(2024.5);
  const arrowStartY = mapY(0.15);

  // Arrow end: mid-point of large codebase line (around 2024)
  const arrowEndX = mapX(2024);
  const arrowEndY = mapY(0.46);

  // Control points for the curve — sweeping right then up
  const cp1x = arrowStartX + 80;
  const cp1y = arrowStartY - 60;
  const cp2x = arrowEndX + 100;
  const cp2y = arrowEndY + 80;

  const curvePath = `M ${arrowStartX} ${arrowStartY} C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${arrowEndX} ${arrowEndY}`;

  // Approximate curve length for dash animation
  const pathLength = 500;
  const dashOffset = pathLength * (1 - drawProgress);

  // Arrowhead angle (approximate tangent at end)
  const arrowHeadSize = 10;
  // Tangent at end of cubic bezier: derivative at t=1 is 3*(P3-P2)
  const tangentX = arrowEndX - cp2x;
  const tangentY = arrowEndY - cp2y;
  const angle = Math.atan2(tangentY, tangentX);

  // Arrow label position — midpoint of curve
  const labelX = (arrowStartX + arrowEndX) / 2 + 60;
  const labelY = (arrowStartY + arrowEndY) / 2 - 10;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      {/* Curved dashed arrow path */}
      <path
        d={curvePath}
        fill="none"
        stroke={ARROW_COLOR}
        strokeWidth={2}
        strokeDasharray="6 4"
        strokeDashoffset={dashOffset}
        style={{
          transition: "none",
        }}
      />

      {/* Arrowhead */}
      {drawProgress > 0.9 && (
        <polygon
          points={`
            ${arrowEndX},${arrowEndY}
            ${arrowEndX - arrowHeadSize * Math.cos(angle - 0.4)},${arrowEndY - arrowHeadSize * Math.sin(angle - 0.4)}
            ${arrowEndX - arrowHeadSize * Math.cos(angle + 0.4)},${arrowEndY - arrowHeadSize * Math.sin(angle + 0.4)}
          `}
          fill={ARROW_COLOR}
          opacity={interpolate(drawProgress, [0.9, 1], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        />
      )}

      {/* Arrow label */}
      {frame >= ARROW_LABEL_START && (
        <>
          {/* Label background for readability */}
          <rect
            x={labelX - 6}
            y={labelY - 14}
            width={200}
            height={24}
            rx={4}
            fill="#0A0F1A"
            opacity={labelOpacity * 0.8}
          />
          <text
            x={labelX}
            y={labelY}
            fill={ARROW_COLOR}
            fontSize={14}
            fontFamily="Inter, sans-serif"
            fontWeight={700}
            opacity={labelOpacity}
          >
            Every patch adds code.
          </text>
        </>
      )}
    </svg>
  );
};

export default TrapArrow;
