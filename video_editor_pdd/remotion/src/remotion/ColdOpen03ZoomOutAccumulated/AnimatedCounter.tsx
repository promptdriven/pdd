import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  FONT_FAMILY,
  COUNTER_FONT_SIZE,
  SUFFIX_FONT_SIZE,
  COUNTER_OPACITY,
  SUFFIX_OPACITY,
  COUNTER_START,
  COUNTER_DURATION,
} from "./constants";

interface AnimatedCounterProps {
  targetValue: number;
  suffix: string;
  color: string;
  /** "left" positions bottom-left, "right" positions bottom-right */
  align: "left" | "right";
}

export const AnimatedCounter: React.FC<AnimatedCounterProps> = ({
  targetValue,
  suffix,
  color,
  align,
}) => {
  const frame = useCurrentFrame();

  // Counter animates from 0 to target with expo ease-out
  const counterProgress = interpolate(
    frame,
    [COUNTER_START, COUNTER_START + COUNTER_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  // Fade in the counter
  const counterOpacity = interpolate(
    frame,
    [COUNTER_START, COUNTER_START + 8],
    [0, COUNTER_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const currentValue = Math.round(counterProgress * targetValue);
  const formattedValue = currentValue.toLocaleString();

  return (
    <div
      style={{
        position: "absolute",
        bottom: 40,
        ...(align === "left" ? { left: 24 } : { right: 24 }),
        display: "flex",
        alignItems: "baseline",
        gap: 8,
        opacity: counterOpacity,
      }}
    >
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: COUNTER_FONT_SIZE,
          fontWeight: 700,
          color,
          lineHeight: 1,
        }}
      >
        {formattedValue}
      </span>
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: SUFFIX_FONT_SIZE,
          fontWeight: 400,
          color,
          opacity: SUFFIX_OPACITY / COUNTER_OPACITY, // relative to parent opacity
          lineHeight: 1,
        }}
      >
        {suffix}
      </span>
    </div>
  );
};

export default AnimatedCounter;
