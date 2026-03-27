import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  INSIGHT_TEXT,
  TEXT_Y,
  TEXT_FONT_SIZE,
  TEXT_FONT_WEIGHT,
  TEXT_FONT_FAMILY,
  TEXT_COLOR,
  TEXT_OPACITY,
  TEXT_FADE_IN_START,
  TEXT_FADE_IN_END,
  TEXT_FADE_OUT_START,
  TEXT_FADE_OUT_END,
  CANVAS_WIDTH,
} from "./constants";

/**
 * The quiet insight text that fades in and out above the horizontal line.
 */
export const InsightText: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in: frames 90-150
  const fadeIn = interpolate(
    frame,
    [TEXT_FADE_IN_START, TEXT_FADE_IN_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Fade out: frames 300-330
  const fadeOut = interpolate(
    frame,
    [TEXT_FADE_OUT_START, TEXT_FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  const opacity = Math.min(fadeIn, fadeOut) * TEXT_OPACITY;

  // Don't render before fade-in starts
  if (frame < TEXT_FADE_IN_START) {
    return null;
  }

  return (
    <div
      style={{
        position: "absolute",
        top: TEXT_Y,
        left: 0,
        width: CANVAS_WIDTH,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        transform: "translateY(-50%)",
      }}
    >
      <span
        style={{
          fontFamily: TEXT_FONT_FAMILY,
          fontSize: TEXT_FONT_SIZE,
          fontWeight: TEXT_FONT_WEIGHT,
          color: TEXT_COLOR,
          opacity,
          letterSpacing: "0.02em",
          textAlign: "center",
        }}
      >
        {INSIGHT_TEXT}
      </span>
    </div>
  );
};

export default InsightText;
