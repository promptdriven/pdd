import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  QUESTION_TEXT,
  QUESTION_FONT_SIZE,
  QUESTION_FONT_WEIGHT,
  QUESTION_COLOR,
  QUESTION_Y,
  QUESTION_FADE_END_FRAME,
  TITLE_FONT_FAMILY,
} from "./constants";

/**
 * Previous question text ("So why are we still patching?") fading out.
 * Starts fully visible at frame 0, fades out with easeIn(quad) over 15 frames.
 */
export const QuestionFadeOut: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, QUESTION_FADE_END_FRAME],
    [0.9, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  if (frame > QUESTION_FADE_END_FRAME + 5) return null;

  return (
    <AbsoluteFill
      style={{
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        opacity,
        pointerEvents: "none",
      }}
    >
      <span
        style={{
          fontFamily: TITLE_FONT_FAMILY,
          fontSize: QUESTION_FONT_SIZE,
          fontWeight: QUESTION_FONT_WEIGHT,
          color: QUESTION_COLOR,
          textAlign: "center",
        }}
      >
        {QUESTION_TEXT}
      </span>
    </AbsoluteFill>
  );
};
