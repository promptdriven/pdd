import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  FONT_FAMILY,
  AMBER_LINE_COLOR,
  ACCUMULATION_ARROW_START,
  ACCUMULATION_ARROW_DRAW,
  dataToPixelX,
  dataToPixelY,
} from "./constants";

/**
 * AccumulationArrow: A curved arrow from the lower fork (small codebase)
 * arcing upward to the upper fork (large codebase), labeled
 * "Every patch adds code".
 */
export const AccumulationArrow: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < ACCUMULATION_ARROW_START) return null;

  // Arrow from lower fork midpoint (~2023, ~3h) to upper fork midpoint (~2023, ~10.5h)
  const fromX = dataToPixelX(2023);
  const fromY = dataToPixelY(3);
  const toX = dataToPixelX(2023.2);
  const toY = dataToPixelY(10.5);

  // Control point for the curve (arc to the right)
  const cpX = fromX + 120;
  const cpY = (fromY + toY) / 2;

  // Build the quadratic bezier path
  const arrowPath = `M ${fromX} ${fromY} Q ${cpX} ${cpY}, ${toX} ${toY}`;

  // Estimate path length (rough)
  const dx = toX - fromX;
  const dy = toY - fromY;
  const straightLen = Math.sqrt(dx * dx + dy * dy);
  const pathLength = straightLen * 1.3;

  // Draw progress
  const drawEnd = ACCUMULATION_ARROW_START + ACCUMULATION_ARROW_DRAW;
  const drawProgress = interpolate(
    frame,
    [ACCUMULATION_ARROW_START, drawEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Arrowhead opacity (appears near end of draw)
  const arrowheadOpacity = interpolate(
    frame,
    [drawEnd - 5, drawEnd],
    [0, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Label fades in after arrow is drawn
  const labelOpacity = interpolate(
    frame,
    [drawEnd, drawEnd + 15],
    [0, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Arrowhead triangle pointing at 'to'
  // Direction vector at endpoint: approximate tangent of Q-bezier at t=1
  // For Q-bezier: tangent at t=1 = 2*(P2-CP) = 2*(to - cp)
  const tangentX = toX - cpX;
  const tangentY = toY - cpY;
  const tangentLen = Math.sqrt(tangentX * tangentX + tangentY * tangentY);
  const nx = tangentX / tangentLen;
  const ny = tangentY / tangentLen;

  // Arrowhead (small triangle)
  const arrowSize = 8;
  const perpX = -ny;
  const perpY = nx;
  const tipX = toX;
  const tipY = toY;
  const leftX = tipX - nx * arrowSize + perpX * arrowSize * 0.5;
  const leftY = tipY - ny * arrowSize + perpY * arrowSize * 0.5;
  const rightX = tipX - nx * arrowSize - perpX * arrowSize * 0.5;
  const rightY = tipY - ny * arrowSize - perpY * arrowSize * 0.5;

  // Label position: along the curve midpoint
  const labelX = cpX + 10;
  const labelY = cpY;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Curved arrow path */}
        <path
          d={arrowPath}
          fill="none"
          stroke={AMBER_LINE_COLOR}
          strokeWidth={2}
          strokeLinecap="round"
          strokeDasharray={`${pathLength} ${pathLength}`}
          strokeDashoffset={pathLength * (1 - drawProgress)}
          opacity={0.3}
        />

        {/* Arrowhead */}
        <polygon
          points={`${tipX},${tipY} ${leftX},${leftY} ${rightX},${rightY}`}
          fill={AMBER_LINE_COLOR}
          opacity={arrowheadOpacity}
        />

        {/* Label: "Every patch adds code" */}
        <text
          x={labelX}
          y={labelY}
          fill={AMBER_LINE_COLOR}
          fontSize={10}
          fontFamily={FONT_FAMILY}
          fontWeight={400}
          textAnchor="start"
          opacity={labelOpacity}
        >
          Every patch adds code
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default AccumulationArrow;
