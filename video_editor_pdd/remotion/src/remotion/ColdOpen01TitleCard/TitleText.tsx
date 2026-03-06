import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TITLE_TEXT,
  FADE_IN_END,
  FADE_OUT_START,
  FADE_OUT_END,
  SCALE_START,
  SCALE_END,
  TITLE_FONT_SIZE,
  TITLE_COLOR,
  TITLE_SHADOW,
  TITLE_LETTER_SPACING,
  TITLE_LINE_HEIGHT,
  TITLE_Y_PERCENT,
  TITLE_MAX_WIDTH,
} from "./constants";

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeInOpacity = interpolate(frame, [0, FADE_IN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const fadeOutOpacity = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  const opacity = fadeInOpacity * fadeOutOpacity;

  const scale = interpolate(frame, [0, FADE_IN_END], [SCALE_START, SCALE_END], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  return (
    <div
      style={{
        position: "absolute",
        top: `${TITLE_Y_PERCENT}%`,
        left: "50%",
        transform: `translate(-50%, -50%) scale(${scale})`,
        opacity,
        fontFamily: "'Inter', sans-serif",
        fontWeight: 700,
        fontSize: TITLE_FONT_SIZE,
        color: TITLE_COLOR,
        textShadow: TITLE_SHADOW,
        letterSpacing: TITLE_LETTER_SPACING,
        lineHeight: TITLE_LINE_HEIGHT,
        textAlign: "center" as const,
        width: TITLE_MAX_WIDTH,
      }}
    >
      {TITLE_TEXT}
    </div>
  );
};

export default TitleText;
