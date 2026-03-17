import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  COUNTER_START_FRAME,
  COUNTER_DURATION,
  COUNTER_FONT_SIZE,
} from "./constants";

export const AnimatedCounter: React.FC<{
  startValue: number;
  endValue: number;
  prefix: string;
  fontFamily: string;
  color: string;
  opacity: number;
  x: number;
  y: number;
  align?: "left" | "right";
}> = ({
  startValue,
  endValue,
  prefix,
  fontFamily,
  color,
  opacity,
  x,
  y,
  align = "left",
}) => {
  const frame = useCurrentFrame();

  // Counter visibility fade-in
  const fadeIn = interpolate(
    frame,
    [COUNTER_START_FRAME, COUNTER_START_FRAME + 10],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Counter value with exponential easing (fast start, slows at end)
  const counterProgress = interpolate(
    frame,
    [COUNTER_START_FRAME, COUNTER_START_FRAME + COUNTER_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Apply easeOut(expo) manually: 1 - (1-t)^4 approximation for expo feel
  const easedProgress = 1 - Math.pow(1 - counterProgress, 4);
  const currentValue = Math.round(
    startValue + (endValue - startValue) * easedProgress
  );

  const formattedValue = currentValue.toLocaleString();

  return (
    <div
      style={{
        position: "absolute",
        left: align === "left" ? x : undefined,
        right: align === "right" ? 958 - x : undefined,
        top: y,
        fontFamily,
        fontSize: COUNTER_FONT_SIZE,
        color,
        opacity: opacity * fadeIn,
        whiteSpace: "nowrap",
        letterSpacing: "0.05em",
      }}
    >
      {prefix}
      {formattedValue}
    </div>
  );
};
