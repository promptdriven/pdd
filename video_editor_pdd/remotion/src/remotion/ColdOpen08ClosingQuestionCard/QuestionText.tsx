import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  QUESTION_TEXT,
  QUESTION_FONT_SIZE,
  QUESTION_COLOR,
  QUESTION_SHADOW,
  QUESTION_LETTER_SPACING,
  QUESTION_Y,
  QUESTION_DRIFT,
  QUESTION_FADE_START,
  QUESTION_FADE_END,
  FADE_OUT_START,
  FADE_OUT_END,
} from "./constants";

export const QuestionText: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [QUESTION_FADE_START, QUESTION_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const opacity = fadeIn * fadeOut;

  const yOffset = interpolate(
    frame,
    [QUESTION_FADE_START, QUESTION_FADE_END],
    [QUESTION_DRIFT, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: QUESTION_Y + yOffset,
        left: "50%",
        transform: "translateX(-50%)",
        opacity,
        fontFamily: "'Inter', sans-serif",
        fontWeight: 700,
        fontSize: QUESTION_FONT_SIZE,
        color: QUESTION_COLOR,
        textShadow: QUESTION_SHADOW,
        letterSpacing: QUESTION_LETTER_SPACING,
        lineHeight: 1.2,
        textAlign: "center" as const,
        whiteSpace: "nowrap" as const,
      }}
    >
      {QUESTION_TEXT}
    </div>
  );
};

export default QuestionText;
