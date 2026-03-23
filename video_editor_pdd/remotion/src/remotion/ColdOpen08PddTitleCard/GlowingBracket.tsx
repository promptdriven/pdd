import React from "react";

interface GlowingBracketProps {
  side: "left" | "right";
  drawProgress: number;
  glowIntensity: number;
  bracketColor: string;
  glowColor: string;
  height: number;
  strokeWidth: number;
  armLength: number;
}

export const GlowingBracket: React.FC<GlowingBracketProps> = ({
  side,
  drawProgress,
  glowIntensity,
  bracketColor,
  glowColor,
  height,
  strokeWidth,
  armLength,
}) => {
  // The bracket is an open bracket shape: ⌐ or ¬ mirrored
  // Path: top arm → vertical stroke → bottom arm
  const totalPathLength = armLength + height + armLength;
  const drawnLength = totalPathLength * drawProgress;

  // Build the SVG path for the bracket
  const isLeft = side === "left";
  const svgWidth = armLength + strokeWidth;
  const svgHeight = height + strokeWidth;

  // For left bracket: top-right → top-left → bottom-left → bottom-right
  // For right bracket: top-left → top-right → bottom-right → bottom-left
  const halfSw = strokeWidth / 2;
  const path = isLeft
    ? `M ${armLength + halfSw} ${halfSw} L ${halfSw} ${halfSw} L ${halfSw} ${height + halfSw} L ${armLength + halfSw} ${height + halfSw}`
    : `M ${halfSw} ${halfSw} L ${armLength + halfSw} ${halfSw} L ${armLength + halfSw} ${height + halfSw} L ${halfSw} ${height + halfSw}`;

  // Glow pulse
  const glowBlur = 12 + glowIntensity * 8;
  const glowSpread = 2 + glowIntensity * 4;

  return (
    <svg
      width={svgWidth + strokeWidth}
      height={svgHeight}
      viewBox={`0 0 ${svgWidth + strokeWidth} ${svgHeight}`}
      style={{ overflow: "visible" }}
    >
      {/* Glow layer */}
      <path
        d={path}
        fill="none"
        stroke={glowColor}
        strokeWidth={strokeWidth + glowSpread}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalPathLength}
        strokeDashoffset={totalPathLength - drawnLength}
        style={{
          filter: `blur(${glowBlur}px)`,
          opacity: 0.6 + glowIntensity * 0.4,
        }}
      />
      {/* Main bracket stroke */}
      <path
        d={path}
        fill="none"
        stroke={bracketColor}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalPathLength}
        strokeDashoffset={totalPathLength - drawnLength}
      />
    </svg>
  );
};

export default GlowingBracket;
