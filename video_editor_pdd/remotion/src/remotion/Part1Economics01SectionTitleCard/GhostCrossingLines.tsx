// GhostCrossingLines.tsx — faint crossing lines foreshadowing the cost-crossing chart
import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";

interface GhostCrossingLinesProps {
  drawProgress: number; // 0..1 how much of the lines are drawn
  pulseFrame: number; // current frame for pulse cycle
  pulseCycleFrames: number;
  lineAColor: string;
  lineBColor: string;
  lineOpacity: number;
  strokeWidth: number;
  glowColor: string;
  glowOpacity: number;
  glowRadius: number;
  width: number;
  height: number;
}

export const GhostCrossingLines: React.FC<GhostCrossingLinesProps> = ({
  drawProgress,
  pulseFrame,
  pulseCycleFrames,
  lineAColor,
  lineBColor,
  lineOpacity,
  strokeWidth,
  glowColor,
  glowOpacity,
  glowRadius,
  width,
  height,
}) => {
  // Pulse between 0.7x and 1.3x of base opacity using sine easing
  const pulsePhase = (pulseFrame % pulseCycleFrames) / pulseCycleFrames;
  const pulseSine = Math.sin(pulsePhase * Math.PI * 2);
  const pulsedOpacity = lineOpacity * (1 + pulseSine * 0.3);

  // Line A: descending from top-left area to bottom-right area
  // Going from (300, 200) to (1620, 880)
  const lineALength = Math.sqrt(
    Math.pow(1620 - 300, 2) + Math.pow(880 - 200, 2)
  );

  // Line B: ascending from bottom-left to top-right area
  // Going from (300, 880) to (1620, 200)
  const lineBLength = Math.sqrt(
    Math.pow(1620 - 300, 2) + Math.pow(200 - 880, 2)
  );

  const dashOffsetA = lineALength * (1 - drawProgress);
  const dashOffsetB = lineBLength * (1 - drawProgress);

  // Crossing point is at center: (960, 540)
  const showGlow = drawProgress > 0.5;
  const glowVisibleOpacity = showGlow
    ? glowOpacity * Math.min(1, (drawProgress - 0.5) * 4)
    : 0;

  return (
    <AbsoluteFill>
      <svg
        width={width}
        height={height}
        viewBox={`0 0 ${width} ${height}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <radialGradient id="ghostGlow" cx="50%" cy="50%" r="50%">
            <stop offset="0%" stopColor={glowColor} stopOpacity={1} />
            <stop offset="100%" stopColor={glowColor} stopOpacity={0} />
          </radialGradient>
        </defs>

        {/* Line A: descending */}
        <line
          x1={300}
          y1={200}
          x2={1620}
          y2={880}
          stroke={lineAColor}
          strokeWidth={strokeWidth}
          opacity={pulsedOpacity}
          strokeDasharray={lineALength}
          strokeDashoffset={dashOffsetA}
        />

        {/* Line B: ascending */}
        <line
          x1={300}
          y1={880}
          x2={1620}
          y2={200}
          stroke={lineBColor}
          strokeWidth={strokeWidth}
          opacity={pulsedOpacity}
          strokeDasharray={lineBLength}
          strokeDashoffset={dashOffsetB}
        />

        {/* Glow at crossing point */}
        <circle
          cx={960}
          cy={540}
          r={glowRadius}
          fill="url(#ghostGlow)"
          opacity={glowVisibleOpacity}
        />
      </svg>
    </AbsoluteFill>
  );
};
