import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, spring } from "remotion";

const CHART_X = 200;
const CHART_Y = 100;
const CHART_W = 1620;
const CHART_H = 780;

const CROSSOVER = { x: 0.42, y: 0.48 };
const DOT_RADIUS = 6;
const GLOW_RADIUS = 30;
const GLOW_COLOR = "#F59E0B";

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

  if (frame < appearFrame) return null;

  const localFrame = frame - appearFrame;

  // Dot scale with spring
  const dotScale = spring({
    frame: localFrame,
    fps: 30,
    config: { damping: 12, stiffness: 200 },
  });

  // Glow pulsing — sinusoidal, ~2s period (0.105 rad/frame at 30fps)
  const glowOpacity = interpolate(
    Math.sin(frame * 0.105),
    [-1, 1],
    [0.4, 0.8]
  );

  // Label fade
  const labelOpacity = interpolate(
    frame,
    [labelStartFrame, labelEndFrame],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const cx = CHART_X + CROSSOVER.x * CHART_W;
  const cy = CHART_Y + CHART_H * (1 - CROSSOVER.y);

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <radialGradient id="crossoverGlow">
            <stop offset="0%" stopColor={GLOW_COLOR} stopOpacity={1} />
            <stop offset="100%" stopColor={GLOW_COLOR} stopOpacity={0} />
          </radialGradient>
        </defs>

        {/* Glow ring */}
        <circle
          cx={cx}
          cy={cy}
          r={GLOW_RADIUS * dotScale}
          fill="url(#crossoverGlow)"
          opacity={glowOpacity}
        />

        {/* White dot */}
        <circle
          cx={cx}
          cy={cy}
          r={DOT_RADIUS * dotScale}
          fill="#FFFFFF"
        />

        {/* Label: "Crossover" with downward arrow */}
        <g opacity={labelOpacity}>
          <text
            x={cx}
            y={cy - 50}
            fill="#FFFFFF"
            fontSize={24}
            fontFamily="Inter, sans-serif"
            fontWeight={700}
            textAnchor="middle"
          >
            Crossover
          </text>
          {/* Downward arrow */}
          <line
            x1={cx}
            y1={cy - 40}
            x2={cx}
            y2={cy - 20}
            stroke="#FFFFFF"
            strokeWidth={2}
          />
          <polygon
            points={`${cx - 5},${cy - 22} ${cx + 5},${cy - 22} ${cx},${cy - 14}`}
            fill="#FFFFFF"
          />
        </g>
      </svg>
    </AbsoluteFill>
  );
};

export default CrossoverPoint;
