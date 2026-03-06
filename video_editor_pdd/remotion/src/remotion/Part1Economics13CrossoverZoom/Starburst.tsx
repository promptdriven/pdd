import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CROSSOVER_PX_X,
  CROSSOVER_PX_Y,
  STARBURST_COLOR,
  STARBURST_FLASH_START,
  STARBURST_FLASH_END,
  STARBURST_SETTLE,
  FADE_START,
  FADE_END,
} from "./constants";

export const Starburst: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < STARBURST_FLASH_START) return null;

  // Radius: 60 → 200px during flash
  const radius = interpolate(
    frame,
    [STARBURST_FLASH_START, STARBURST_FLASH_END],
    [60, 200],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Base opacity: 0 → 1.0 → 0.8
  const baseOpacity = interpolate(
    frame,
    [STARBURST_FLASH_START, 35, STARBURST_FLASH_END, FADE_START, FADE_END],
    [0, 1.0, 0.8, 0.8, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Gentle sinusoidal pulse during hold phase (1.5s period = 0.14 rad/frame at 30fps)
  const pulseOpacity =
    frame > STARBURST_SETTLE
      ? interpolate(Math.sin(frame * 0.14), [-1, 1], [0.7, 0.9])
      : 1.0;

  const finalOpacity = baseOpacity * pulseOpacity;

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <radialGradient id="starburstGradient">
            <stop offset="0%" stopColor="#FFFFFF" stopOpacity={1} />
            <stop offset="30%" stopColor={STARBURST_COLOR} stopOpacity={0.8} />
            <stop offset="100%" stopColor={STARBURST_COLOR} stopOpacity={0} />
          </radialGradient>
        </defs>

        {/* Outer glow */}
        <circle
          cx={CROSSOVER_PX_X}
          cy={CROSSOVER_PX_Y}
          r={radius}
          fill="url(#starburstGradient)"
          opacity={finalOpacity}
        />

        {/* Inner bright core */}
        <circle
          cx={CROSSOVER_PX_X}
          cy={CROSSOVER_PX_Y}
          r={radius * 0.15}
          fill="#FFFFFF"
          opacity={finalOpacity}
        />

        {/* Starburst rays */}
        {[0, 45, 90, 135, 180, 225, 270, 315].map((angle) => {
          const rad = (angle * Math.PI) / 180;
          const innerR = radius * 0.25;
          const outerR = radius * 0.85;
          const x1 = CROSSOVER_PX_X + Math.cos(rad) * innerR;
          const y1 = CROSSOVER_PX_Y + Math.sin(rad) * innerR;
          const x2 = CROSSOVER_PX_X + Math.cos(rad) * outerR;
          const y2 = CROSSOVER_PX_Y + Math.sin(rad) * outerR;
          return (
            <line
              key={angle}
              x1={x1}
              y1={y1}
              x2={x2}
              y2={y2}
              stroke={STARBURST_COLOR}
              strokeWidth={2}
              opacity={finalOpacity * 0.6}
              strokeLinecap="round"
            />
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};

export default Starburst;
