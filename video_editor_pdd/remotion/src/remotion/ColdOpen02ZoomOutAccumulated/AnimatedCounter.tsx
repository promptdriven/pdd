import React from "react";
import { interpolate, Easing, useCurrentFrame } from "remotion";

interface AnimatedCounterProps {
  startValue: number;
  endValue: number;
  prefix: string;
  fontFamily: string;
  fontSize: number;
  color: string;
  opacity: number;
  x: number;
  y: number;
  startFrame: number;
  duration: number;
  align?: "left" | "right";
}

export const AnimatedCounter: React.FC<AnimatedCounterProps> = ({
  startValue,
  endValue,
  prefix,
  fontFamily,
  fontSize,
  color,
  opacity: targetOpacity,
  x,
  y,
  startFrame,
  duration,
  align = "left",
}) => {
  const frame = useCurrentFrame();

  // Fade in the counter
  const fadeIn = interpolate(frame, [startFrame, startFrame + 10], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Counter value with exponential easing (fast start, slows at end)
  const progress = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.exp),
    }
  );

  const currentValue = Math.round(
    startValue + (endValue - startValue) * progress
  );

  const formattedValue = currentValue.toLocaleString("en-US");

  return (
    <div
      style={{
        position: "absolute",
        left: align === "left" ? x : undefined,
        right: align === "right" ? 1920 - x : undefined,
        top: y,
        fontFamily: `'${fontFamily}', monospace`,
        fontSize,
        color,
        opacity: fadeIn * targetOpacity,
        whiteSpace: "nowrap",
        fontWeight: 500,
        letterSpacing: 0.5,
      }}
    >
      {prefix}
      {formattedValue}
    </div>
  );
};
