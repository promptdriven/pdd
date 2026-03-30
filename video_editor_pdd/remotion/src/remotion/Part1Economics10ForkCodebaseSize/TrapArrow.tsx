import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  ARROW_COLOR,
  FONT_FAMILY,
  ARROW_START,
  ARROW_DRAW_DURATION,
  ARROW_LABEL_FRAME,
  xToPixel,
  yToPixel,
} from "./constants";

/**
 * Curved dashed arrow sweeping from the small-codebase fork (lower)
 * upward toward the large-codebase fork (upper).
 * Label: "Every patch adds code."
 */
export const TrapArrow: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < ARROW_START) return null;

  // Arrow draw progress
  const drawProgress = interpolate(
    frame,
    [ARROW_START, ARROW_START + ARROW_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Label fade
  const labelOpacity = interpolate(
    frame,
    [ARROW_LABEL_FRAME, ARROW_LABEL_FRAME + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Start: near end of small codebase line (~2024, y≈0.18)
  const startX = xToPixel(2024);
  const startY = yToPixel(0.18);

  // End: midpoint of large codebase line (~2023, y≈0.465)
  const endX = xToPixel(2023);
  const endY = yToPixel(0.465);

  // Control points for a nice upward curve (bowing to the right)
  const cp1x = startX + 80;
  const cp1y = startY - 60;
  const cp2x = endX + 100;
  const cp2y = endY + 40;

  const pathD = `M ${startX} ${startY} C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${endX} ${endY}`;

  const pathLength = 600; // approximate path length
  const offset = pathLength * (1 - drawProgress);

  // Arrowhead at end point
  // Calculate tangent at end for arrowhead direction
  // Approximate tangent from last control point to end
  const tangentX = endX - cp2x;
  const tangentY = endY - cp2y;
  const tangentLen = Math.sqrt(tangentX * tangentX + tangentY * tangentY);
  const nx = tangentX / tangentLen;
  const ny = tangentY / tangentLen;
  const arrowSize = 10;
  // Two wing points perpendicular to tangent
  const wing1x = endX - arrowSize * nx + arrowSize * 0.5 * ny;
  const wing1y = endY - arrowSize * ny - arrowSize * 0.5 * nx;
  const wing2x = endX - arrowSize * nx - arrowSize * 0.5 * ny;
  const wing2y = endY - arrowSize * ny + arrowSize * 0.5 * nx;
  const arrowheadD = `M ${endX} ${endY} L ${wing1x} ${wing1y} L ${wing2x} ${wing2y} Z`;

  // Label position: midpoint of the curve (approximate)
  const labelX = (startX + endX) / 2 + 60;
  const labelY = (startY + endY) / 2 - 20;

  return (
    <>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          pointerEvents: "none",
        }}
      >
        {/* Curved dashed arrow path */}
        <path
          d={pathD}
          fill="none"
          stroke={ARROW_COLOR}
          strokeWidth={2}
          strokeDasharray="6 4"
          strokeDashoffset={offset}
          strokeLinecap="round"
        />

        {/* Arrowhead - appears when arrow is mostly drawn */}
        {drawProgress > 0.85 && (
          <path
            d={arrowheadD}
            fill={ARROW_COLOR}
            opacity={interpolate(drawProgress, [0.85, 1], [0, 1], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            })}
          />
        )}
      </svg>

      {/* Arrow label */}
      <div
        style={{
          position: "absolute",
          left: labelX,
          top: labelY,
          opacity: labelOpacity,
          color: ARROW_COLOR,
          fontSize: 14,
          fontWeight: 700,
          fontFamily: FONT_FAMILY,
          whiteSpace: "nowrap",
          textShadow: "0 1px 4px rgba(0,0,0,0.6)",
        }}
      >
        Every patch adds code.
      </div>
    </>
  );
};

export default TrapArrow;
