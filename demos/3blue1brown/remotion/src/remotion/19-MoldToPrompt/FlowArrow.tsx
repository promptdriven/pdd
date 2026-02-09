import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { BEATS, COLORS, VERILOG_BLOCK, NETLIST_BLOCK } from "./constants";

/**
 * Renders a downward arrow/flow indicator from the prompt document to the code block.
 * Appears during the relationship phase (frame 360-480).
 * Includes a "generates" label next to the arrow.
 */
export const FlowArrow: React.FC = () => {
  const frame = useCurrentFrame();

  // Arrow fade-in
  const arrowOpacity = interpolate(
    frame,
    [BEATS.RELATIONSHIP_START, BEATS.RELATIONSHIP_START + 40],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Arrow draw-down animation (line grows from top to bottom)
  const drawProgress = interpolate(
    frame,
    [BEATS.RELATIONSHIP_START, BEATS.RELATIONSHIP_START + 60],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // "generates" label fade-in (slightly after arrow)
  const labelOpacity = interpolate(
    frame,
    [BEATS.RELATIONSHIP_START + 40, BEATS.RELATIONSHIP_START + 70],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  if (frame < BEATS.RELATIONSHIP_START) return null;

  // Arrow coordinates: from bottom of prompt document to top of code
  const docBottom = VERILOG_BLOCK.finalY + VERILOG_BLOCK.finalHeight;
  const codeTop = NETLIST_BLOCK.finalY;
  const centerX = VERILOG_BLOCK.finalX + VERILOG_BLOCK.finalWidth / 2;

  const arrowStartY = docBottom + 10;
  const arrowEndY = codeTop - 10;
  const arrowLength = arrowEndY - arrowStartY;

  // Current drawn length
  const currentEndY = arrowStartY + arrowLength * drawProgress;

  // Arrowhead size
  const headSize = 10;

  // Subtle pulse on the arrow (after fully drawn)
  const pulse =
    drawProgress >= 1
      ? 0.8 + 0.2 * Math.sin((frame - BEATS.RELATIONSHIP_START - 60) * 0.08)
      : 1;

  return (
    <g opacity={arrowOpacity}>
      {/* Glow behind the arrow line */}
      <line
        x1={centerX}
        y1={arrowStartY}
        x2={centerX}
        y2={currentEndY}
        stroke={COLORS.PROMPT_GLOW}
        strokeWidth={6}
        opacity={0.3 * pulse}
        strokeLinecap="round"
      />

      {/* Main arrow line */}
      <line
        x1={centerX}
        y1={arrowStartY}
        x2={centerX}
        y2={currentEndY}
        stroke={COLORS.ARROW_COLOR}
        strokeWidth={2.5}
        strokeLinecap="round"
        opacity={pulse}
      />

      {/* Arrowhead (appears when line is fully drawn) */}
      {drawProgress > 0.9 && (
        <polygon
          points={`
            ${centerX},${currentEndY}
            ${centerX - headSize},${currentEndY - headSize * 1.5}
            ${centerX + headSize},${currentEndY - headSize * 1.5}
          `}
          fill={COLORS.ARROW_COLOR}
          opacity={interpolate(drawProgress, [0.9, 1], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }) * pulse}
        />
      )}

      {/* "generates" label */}
      {labelOpacity > 0 && (
        <text
          x={centerX + 24}
          y={(arrowStartY + arrowEndY) / 2 + 5}
          fontSize={16}
          fontFamily="'Inter', 'Helvetica Neue', Arial, sans-serif"
          fontWeight={400}
          fontStyle="italic"
          fill={COLORS.ARROW_LABEL}
          opacity={labelOpacity}
          letterSpacing={1}
        >
          generates
        </text>
      )}
    </g>
  );
};
