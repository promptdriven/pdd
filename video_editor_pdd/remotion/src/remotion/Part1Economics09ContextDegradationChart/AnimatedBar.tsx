import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  spring,
  interpolate,
  Easing,
} from "remotion";
import {
  WIDTH,
  HEIGHT,
  CHART_Y,
  CHART_H,
  FPS,
  GLOW_PULSE_START,
} from "./constants";

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
    fps: FPS,
    config: { damping: 12, stiffness: 150 },
  });

  const targetHeight = (capability / 100) * CHART_H;
  const currentHeight = targetHeight * growProgress;
  const barY = CHART_Y + CHART_H - currentHeight;

  // Label fade in after bar mostly grown
  const labelOpacity = interpolate(localFrame, [20, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Subtle glow pulsing after all bars settle
  const glowPhase = Math.sin(frame * 0.06);
  const glowOpacity =
    frame > GLOW_PULSE_START
      ? interpolate(glowPhase, [-1, 1], [0.0, 0.15])
      : 0;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <filter
            id={`glow-${capability}`}
            x="-50%"
            y="-50%"
            width="200%"
            height="200%"
          >
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
