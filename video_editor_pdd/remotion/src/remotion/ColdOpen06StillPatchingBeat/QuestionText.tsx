import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TEXT_FADE_START,
  TEXT_FADE_END,
  TEXT_COLOR,
  ACCENT_COLOR,
  TEXT_OPACITY,
  TEXT_SIZE,
  TEXT_WEIGHT,
  LETTER_SPACING,
} from "./constants";

/**
 * The question "So why are we still patching?" — fades in at frame 30-60.
 * "patching?" rendered in warm amber accent color.
 */
export const QuestionText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TEXT_FADE_START, TEXT_FADE_END],
    [0, TEXT_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        opacity,
      }}
    >
      <div
        style={{
          fontSize: TEXT_SIZE,
          fontFamily: '"Inter", system-ui, sans-serif',
          fontWeight: TEXT_WEIGHT,
          letterSpacing: LETTER_SPACING,
          textAlign: "center",
          lineHeight: 1.4,
        }}
      >
        <span style={{ color: TEXT_COLOR }}>So why are we still </span>
        <span style={{ color: ACCENT_COLOR }}>patching?</span>
      </div>
    </AbsoluteFill>
  );
};
