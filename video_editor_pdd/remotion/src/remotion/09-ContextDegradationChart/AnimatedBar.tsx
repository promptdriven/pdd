import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  spring,
  Easing,
} from "remotion";
import {
  WIDTH,
  HEIGHT,
  CHART_Y,
  CHART_H,
  BAR_WIDTH,
  GLOW_PULSE_START,
  GLOW_PULSE_PERIOD,
} from "./constants";

interface AnimatedBarProps {
  centerX: number;
  capabilityPercent: number;
  color: string;
  startFrame: number;
  label: string;
}

export const AnimatedBar: React.FC<AnimatedBarProps> = ({
  centerX,
  capabilityPercent,
  color,
  startFrame,
  label,
}) => {
  const frame = useCurrentFrame();

  const localFrame = frame - startFrame;
  if (localFrame < 0) return null;

  const growProgress = spring({
    frame: localFrame,
    fps: 30,
    config: { damping: 12, stiffness: 150 },
  });

  const targetHeight = CHART_H * (capabilityPercent / 100);
  const currentHeight = targetHeight * growProgress;

  const barX = centerX - BAR_WIDTH / 2;
  const barBottom = CHART_Y + CHART_H;
  const barTop = barBottom - currentHeight;

  const labelOpacity = interpolate(localFrame, [20, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Subtle glow pulse after hold begins
  const glowPhase =
    frame >= GLOW_PULSE_START
      ? Math.sin(
          ((frame - GLOW_PULSE_START) / GLOW_PULSE_PERIOD) * Math.PI * 2,
        ) *
          0.3 +
        0.7
      : 0;
  const glowOpacity = frame >= GLOW_PULSE_START ? glowPhase * 0.15 : 0;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <linearGradient
            id={`barGrad-${label}`}
            x1="0"
            y1="0"
            x2="0"
            y2="1"
          >
            <stop offset="0%" stopColor={color} stopOpacity={1} />
            <stop offset="100%" stopColor={color} stopOpacity={0.7} />
          </linearGradient>
          <filter id={`glow-${label}`}>
            <feGaussianBlur stdDeviation="8" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Glow layer */}
        {glowOpacity > 0 && (
          <rect
            x={barX - 4}
            y={barTop - 4}
            width={BAR_WIDTH + 8}
            height={currentHeight + 8}
            rx={4}
            fill={color}
            opacity={glowOpacity}
            filter={`url(#glow-${label})`}
          />
        )}

        {/* Main bar */}
        <rect
          x={barX}
          y={barTop}
          width={BAR_WIDTH}
          height={currentHeight}
          rx={3}
          fill={`url(#barGrad-${label})`}
        />

        {/* Value label above bar */}
        <text
          x={centerX}
          y={barBottom - targetHeight - 14}
          fill={color}
          fontSize={28}
          fontFamily="Inter, sans-serif"
          fontWeight={700}
          textAnchor="middle"
          opacity={labelOpacity}
        >
          {`${capabilityPercent}%`}
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default AnimatedBar;
