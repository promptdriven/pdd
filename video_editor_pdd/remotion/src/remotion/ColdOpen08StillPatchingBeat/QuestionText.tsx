import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  QUESTION_TEXT,
  QUESTION_FONT_FAMILY,
  QUESTION_FONT_WEIGHT,
  QUESTION_FONT_SIZE,
  QUESTION_COLOR,
  QUESTION_MAX_OPACITY,
  QUESTION_LETTER_SPACING,
  FADE_IN_END,
  HOLD_END,
  TOTAL_FRAMES,
} from "./constants";

export const QuestionText: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in: easeOut(cubic) from 0 to 0.92 over frames 0-20
  const fadeInOpacity = interpolate(frame, [0, FADE_IN_END], [0, QUESTION_MAX_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(3)),
  });

  // Fade out: easeIn(cubic) from 0.92 to 0 over frames 80-120
  const fadeOutOpacity = interpolate(frame, [HOLD_END, TOTAL_FRAMES], [QUESTION_MAX_OPACITY, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.poly(3)),
  });

  // Combine: during hold (20-80), both clamp to QUESTION_MAX_OPACITY
  const opacity = Math.min(fadeInOpacity, fadeOutOpacity);

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        pointerEvents: "none",
      }}
    >
      <span
        style={{
          fontFamily: QUESTION_FONT_FAMILY,
          fontWeight: QUESTION_FONT_WEIGHT,
          fontSize: QUESTION_FONT_SIZE,
          color: QUESTION_COLOR,
          opacity,
          letterSpacing: QUESTION_LETTER_SPACING,
          textAlign: "center",
          lineHeight: 1.3,
        }}
      >
        {QUESTION_TEXT}
      </span>
    </div>
  );
};

export default QuestionText;
