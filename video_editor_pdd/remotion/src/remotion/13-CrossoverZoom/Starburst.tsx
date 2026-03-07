import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  CROSSOVER_PX_X,
  CROSSOVER_PX_Y,
  STARBURST_COLOR,
  STARBURST_MIN_RADIUS,
  STARBURST_MAX_RADIUS,
  STARBURST_START,
  STARBURST_FLASH_END,
  FADE_TO_BLACK_START,
  FADE_TO_BLACK_END,
} from "./constants";

export const Starburst: React.FC = () => {
  const frame = useCurrentFrame();

  // Radius expansion: 60 → 200px over frames 20-50
  const radius = interpolate(
    frame,
    [STARBURST_START, STARBURST_FLASH_END],
    [STARBURST_MIN_RADIUS, STARBURST_MAX_RADIUS],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    },
  );

  // Opacity: 0 → 1.0 (flash) → 0.8 (settle), then gentle pulse
  const flashOpacity = interpolate(
    frame,
    [STARBURST_START, STARBURST_START + 15, STARBURST_FLASH_END],
    [0, 1.0, 0.8],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    },
  );

  // Sinusoidal pulse during hold (frames 50+): oscillates 0.7-0.9
  const pulseOpacity =
    frame > STARBURST_FLASH_END
      ? interpolate(Math.sin(frame * 0.14), [-1, 1], [0.7, 0.9])
      : flashOpacity;

  // Fade out with the fade-to-black
  const fadeOut = interpolate(
    frame,
    [FADE_TO_BLACK_START, FADE_TO_BLACK_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    },
  );

  const opacity = pulseOpacity * fadeOut;

  if (frame < STARBURST_START) return null;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          {/* Inner bright starburst */}
          <radialGradient id="starburstGlow">
            <stop offset="0%" stopColor="#FFFFFF" stopOpacity={1} />
            <stop offset="30%" stopColor={STARBURST_COLOR} stopOpacity={0.9} />
            <stop offset="100%" stopColor={STARBURST_COLOR} stopOpacity={0} />
          </radialGradient>
          {/* Outer soft halo */}
          <radialGradient id="starburstHalo">
            <stop offset="0%" stopColor={STARBURST_COLOR} stopOpacity={0.4} />
            <stop offset="100%" stopColor={STARBURST_COLOR} stopOpacity={0} />
          </radialGradient>
        </defs>

        {/* Outer halo (larger, softer) */}
        <circle
          cx={CROSSOVER_PX_X}
          cy={CROSSOVER_PX_Y}
          r={radius * 1.5}
          fill="url(#starburstHalo)"
          opacity={opacity * 0.6}
        />

        {/* Main starburst */}
        <circle
          cx={CROSSOVER_PX_X}
          cy={CROSSOVER_PX_Y}
          r={radius}
          fill="url(#starburstGlow)"
          opacity={opacity}
        />

        {/* Bright core */}
        <circle
          cx={CROSSOVER_PX_X}
          cy={CROSSOVER_PX_Y}
          r={radius * 0.15}
          fill="#FFFFFF"
          opacity={opacity}
        />
      </svg>
    </AbsoluteFill>
  );
};

export default Starburst;
