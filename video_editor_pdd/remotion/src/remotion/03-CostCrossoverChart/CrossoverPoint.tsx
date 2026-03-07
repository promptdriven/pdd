import React from "react";
import { AbsoluteFill, useCurrentFrame, useVideoConfig, interpolate, spring } from "remotion";
import {
  WIDTH,
  HEIGHT,
  CHART_X,
  CHART_Y,
  CHART_W,
  CHART_H,
  CROSSOVER_POINT,
  CROSSOVER_DOT_RADIUS,
  CROSSOVER_GLOW_RADIUS,
  CROSSOVER_GLOW_COLOR,
  CROSSOVER_DOT_COLOR,
  LABEL_COLOR,
  FONT_FAMILY,
} from "./constants";

interface CrossoverPointProps {
  appearFrame: number;
  labelStartFrame: number;
  labelEndFrame: number;
}

export const CrossoverPoint: React.FC<CrossoverPointProps> = ({
  appearFrame,
  labelStartFrame,
  labelEndFrame,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  if (frame < appearFrame) return null;

  const localFrame = frame - appearFrame;

  // Dot scale with spring animation
  const dotScale = spring({
    frame: localFrame,
    fps,
    config: { damping: 12, stiffness: 200 },
  });

  // Glow pulsing — sinusoidal, ~2s period (0.105 rad/frame at 30fps)
  const glowOpacity = interpolate(
    Math.sin(frame * 0.105),
    [-1, 1],
    [0.4, 0.8],
  );

  // Label fade in
  const labelOpacity = interpolate(
    frame,
    [labelStartFrame, labelEndFrame],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    },
  );

  const cx = CHART_X + CROSSOVER_POINT.x * CHART_W;
  const cy = CHART_Y + CHART_H * (1 - CROSSOVER_POINT.y);

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <radialGradient id="crossoverGlow">
            <stop offset="0%" stopColor={CROSSOVER_GLOW_COLOR} stopOpacity={1} />
            <stop offset="100%" stopColor={CROSSOVER_GLOW_COLOR} stopOpacity={0} />
          </radialGradient>
        </defs>

        {/* Pulsing glow ring */}
        <circle
          cx={cx}
          cy={cy}
          r={CROSSOVER_GLOW_RADIUS * dotScale}
          fill="url(#crossoverGlow)"
          opacity={glowOpacity}
        />

        {/* White dot */}
        <circle
          cx={cx}
          cy={cy}
          r={CROSSOVER_DOT_RADIUS * dotScale}
          fill={CROSSOVER_DOT_COLOR}
        />

        {/* "Crossover" label with downward arrow */}
        <g opacity={labelOpacity}>
          <text
            x={cx}
            y={cy - 50}
            fill={LABEL_COLOR}
            fontSize={24}
            fontFamily={FONT_FAMILY}
            fontWeight={700}
            textAnchor="middle"
          >
            Crossover
          </text>
          {/* Arrow shaft */}
          <line
            x1={cx}
            y1={cy - 40}
            x2={cx}
            y2={cy - 20}
            stroke={LABEL_COLOR}
            strokeWidth={2}
          />
          {/* Arrow head */}
          <polygon
            points={`${cx - 5},${cy - 22} ${cx + 5},${cy - 22} ${cx},${cy - 14}`}
            fill={LABEL_COLOR}
          />
        </g>
      </svg>
    </AbsoluteFill>
  );
};

export default CrossoverPoint;
