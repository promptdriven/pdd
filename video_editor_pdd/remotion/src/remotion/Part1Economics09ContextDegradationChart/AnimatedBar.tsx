import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate, Easing } from "remotion";

const CHART_X = 300;
const CHART_Y = 150;
const CHART_H = 700;

interface AnimatedBarProps {
  x: number;
  width: number;
  capability: number;
  color: string;
  growStartFrame: number;
}

export const AnimatedBar: React.FC<AnimatedBarProps> = ({
  x,
  width,
  capability,
  color,
  growStartFrame,
}) => {
  const frame = useCurrentFrame();

  if (frame < growStartFrame) return null;

  const localFrame = frame - growStartFrame;

  // Bar height spring animation
  const growProgress = spring({
    frame: localFrame,
    fps: 30,
    config: { damping: 12, stiffness: 150 },
  });

  const targetHeight = (capability / 100) * CHART_H;
  const currentHeight = targetHeight * growProgress;
  const barY = CHART_Y + CHART_H - currentHeight;

  // Label fade in
  const labelOpacity = interpolate(localFrame, [20, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Subtle glow pulsing after bars settle (starts around frame 210 globally)
  const glowPhase = Math.sin(frame * 0.06);
  const glowOpacity = frame > 210 ? interpolate(glowPhase, [-1, 1], [0.0, 0.15]) : 0;

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          {/* Glow filter for pulsing effect */}
          <filter id={`glow-${capability}`} x="-50%" y="-50%" width="200%" height="200%">
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
            x={x - 4}
            y={barY - 4}
            width={width + 8}
            height={currentHeight + 4}
            rx={6}
            fill={color}
            opacity={glowOpacity}
            filter={`url(#glow-${capability})`}
          />
        )}

        {/* Main bar */}
        <rect
          x={x}
          y={barY}
          width={width}
          height={currentHeight}
          rx={4}
          fill={color}
          opacity={0.9}
        />

        {/* Bar value label above bar */}
        <text
          x={x + width / 2}
          y={barY - 14}
          fill={color}
          fontSize={28}
          fontFamily="Inter, sans-serif"
          fontWeight={700}
          textAnchor="middle"
          opacity={labelOpacity}
        >
          {capability}%
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default AnimatedBar;
