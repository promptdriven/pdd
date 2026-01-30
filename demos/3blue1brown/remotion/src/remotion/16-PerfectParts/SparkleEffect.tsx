import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import { BEATS, COLORS, MOLD } from "./constants";

/**
 * Sparkle / starburst effect on the mold's adjustment point.
 * Appears during frame 0-60 to indicate the mold has been fixed.
 * Multiple small starburst particles radiate outward and fade.
 */
export const SparkleEffect: React.FC = () => {
  const frame = useCurrentFrame();

  // Only visible during the mold-fixed phase
  if (frame > BEATS.MOLD_FIXED_END + 20) return null;

  const cx = MOLD.fixPointX;
  const cy = MOLD.fixPointY;

  // Central glow pulse
  const glowOpacity = interpolate(
    frame,
    [0, 10, 30, BEATS.MOLD_FIXED_END],
    [0, 0.9, 0.7, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  const glowRadius = interpolate(frame, [0, 10, BEATS.MOLD_FIXED_END], [4, 18, 12], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Starburst rays
  const rayCount = 8;
  const rays: {
    x1: number;
    y1: number;
    x2: number;
    y2: number;
    opacity: number;
    color: string;
  }[] = [];

  for (let i = 0; i < rayCount; i++) {
    const angle = (i / rayCount) * Math.PI * 2 + frame * 0.03;
    const innerR = 8;

    const outerProgress = interpolate(
      frame,
      [0, 8, 35, BEATS.MOLD_FIXED_END],
      [0, 1, 0.8, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
    );
    const outerR = innerR + outerProgress * (20 + (i % 3) * 8);

    const rayOpacity = interpolate(
      frame,
      [0, 8, 40, BEATS.MOLD_FIXED_END],
      [0, 0.9, 0.5, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
    );

    rays.push({
      x1: cx + Math.cos(angle) * innerR,
      y1: cy + Math.sin(angle) * innerR,
      x2: cx + Math.cos(angle) * outerR,
      y2: cy + Math.sin(angle) * outerR,
      opacity: rayOpacity,
      color: i % 2 === 0 ? COLORS.SPARKLE_WHITE : COLORS.SPARKLE_GOLD,
    });
  }

  // Small floating particles
  const particleCount = 6;
  const particles: { cx: number; cy: number; r: number; opacity: number; color: string }[] =
    [];

  for (let i = 0; i < particleCount; i++) {
    const seed = i * 47 + 11;
    const angle = ((seed % 360) / 360) * Math.PI * 2;
    const speed = 0.8 + (seed % 5) * 0.3;

    const travelProgress = interpolate(
      frame,
      [5 + i * 3, 20 + i * 3, 45 + i * 2],
      [0, 1, 1.5],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
    );

    const dist = travelProgress * 30 * speed;
    const pOpacity = interpolate(
      frame,
      [5 + i * 3, 15 + i * 3, 40 + i * 2, BEATS.MOLD_FIXED_END],
      [0, 0.8, 0.3, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
    );

    particles.push({
      cx: cx + Math.cos(angle) * dist,
      cy: cy + Math.sin(angle) * dist,
      r: 2 + (seed % 3),
      opacity: pOpacity,
      color: i % 3 === 0 ? COLORS.SPARKLE_GOLD : COLORS.SPARKLE_WHITE,
    });
  }

  return (
    <g>
      {/* Central glow */}
      <circle
        cx={cx}
        cy={cy}
        r={glowRadius}
        fill={COLORS.SPARKLE_GOLD}
        opacity={glowOpacity * 0.6}
      />
      <circle
        cx={cx}
        cy={cy}
        r={glowRadius * 0.5}
        fill={COLORS.SPARKLE_WHITE}
        opacity={glowOpacity}
      />

      {/* Starburst rays */}
      {rays.map((ray, i) => (
        <line
          key={`ray-${i}`}
          x1={ray.x1}
          y1={ray.y1}
          x2={ray.x2}
          y2={ray.y2}
          stroke={ray.color}
          strokeWidth={2}
          opacity={ray.opacity}
          strokeLinecap="round"
        />
      ))}

      {/* Floating particles */}
      {particles.map((p, i) => (
        <circle
          key={`sparkle-p-${i}`}
          cx={p.cx}
          cy={p.cy}
          r={p.r}
          fill={p.color}
          opacity={p.opacity}
        />
      ))}
    </g>
  );
};
