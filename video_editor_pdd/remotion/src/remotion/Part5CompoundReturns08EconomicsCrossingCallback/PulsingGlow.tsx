import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface PulsingGlowProps {
  cx: number;
  cy: number;
  color: string;
  radius: number;
  minOpacity: number;
  maxOpacity: number;
  cycleFrames: number;
  startFrame: number;
  brighterAfterFrame?: number;
  brighterMaxOpacity?: number;
}

export const PulsingGlow: React.FC<PulsingGlowProps> = ({
  cx,
  cy,
  color,
  radius,
  minOpacity,
  maxOpacity,
  cycleFrames,
  startFrame,
  brighterAfterFrame = Infinity,
  brighterMaxOpacity = 0.35,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  const effectiveMax =
    frame >= brighterAfterFrame ? brighterMaxOpacity : maxOpacity;

  // Progress through the cycle — 0→1 maps to one full pulse
  const cycleProgress = (localFrame % cycleFrames) / cycleFrames;

  // Pulse: ease from min → max → min using sine easing
  const pulseValue = interpolate(
    cycleProgress,
    [0, 0.5, 1],
    [minOpacity, effectiveMax, minOpacity],
    {
      easing: Easing.inOut(Easing.sin),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: cx - radius * 2,
        top: cy - radius * 2,
        width: radius * 4,
        height: radius * 4,
        borderRadius: "50%",
        background: `radial-gradient(circle, ${color} 0%, transparent 70%)`,
        opacity: pulseValue,
        pointerEvents: "none",
      }}
    />
  );
};
