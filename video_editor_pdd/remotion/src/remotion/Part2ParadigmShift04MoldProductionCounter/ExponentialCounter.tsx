import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  COUNTER_COLOR,
  LABEL_COLOR,
  COUNTER_X,
  COUNTER_Y,
  COUNTER_FONT_SIZE,
  LABEL_FONT_SIZE,
  LABEL_OPACITY,
  COUNTER_START,
  COUNTER_END,
  TOTAL_FRAMES,
  FONT_MONO,
  FONT_SANS,
} from "./constants";

/**
 * Exponential counter that accelerates from COUNTER_START to COUNTER_END.
 * Uses easeIn(expo) for dramatic acceleration.
 * Formats numbers with commas for readability.
 */
export const ExponentialCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Use exponential easing: slow at start, dramatically accelerating
  // Map frame to [0,1] with easeIn(expo)
  const t = interpolate(frame, [0, TOTAL_FRAMES - 1], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.exp),
  });

  // Map t to counter value on a log scale for more dramatic acceleration
  // Using exponential mapping: value = start * (end/start)^t
  const logStart = Math.log(COUNTER_START);
  const logEnd = Math.log(COUNTER_END);
  const currentValue = Math.round(Math.exp(logStart + t * (logEnd - logStart)));

  // Clamp to range
  const displayValue = Math.min(Math.max(currentValue, COUNTER_START), COUNTER_END);

  // Format with commas
  const formattedValue = displayValue.toLocaleString("en-US");

  // Subtle scale pulse when hitting milestones
  const milestones = [10, 100, 1000, 10000];
  const isNearMilestone = milestones.some(
    (m) => displayValue >= m * 0.95 && displayValue <= m * 1.05
  );
  const scale = isNearMilestone ? 1.05 : 1;

  // Fade in the counter (visible from frame 0 per requirements)
  const opacity = interpolate(frame, [0, 8], [0.85, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: COUNTER_X,
        top: COUNTER_Y,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        width: 400,
      }}
    >
      {/* Main counter number */}
      <div
        style={{
          fontFamily: FONT_MONO,
          fontSize: COUNTER_FONT_SIZE,
          fontWeight: 700,
          color: COUNTER_COLOR,
          opacity,
          transform: `scale(${scale})`,
          transition: "transform 0.1s ease",
          textShadow: "0 0 30px rgba(226, 232, 240, 0.3), 0 2px 8px rgba(0,0,0,0.5)",
          letterSpacing: "-2px",
          lineHeight: 1,
          whiteSpace: "nowrap",
        }}
      >
        {formattedValue}
      </div>

      {/* Label: "parts produced" */}
      <div
        style={{
          fontFamily: FONT_SANS,
          fontSize: LABEL_FONT_SIZE,
          fontWeight: 400,
          color: LABEL_COLOR,
          opacity: LABEL_OPACITY,
          marginTop: 12,
          letterSpacing: "2px",
          textTransform: "uppercase",
        }}
      >
        parts produced
      </div>
    </div>
  );
};

export default ExponentialCounter;
