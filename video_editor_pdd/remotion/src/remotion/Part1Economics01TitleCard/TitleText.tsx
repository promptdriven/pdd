import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TITLE_TEXT,
  TITLE_FADE_START,
  TITLE_FADE_END,
  CARD_FADE_OUT_START,
  CARD_FADE_OUT_END,
  TITLE_Y,
  TITLE_COLOR,
  TITLE_FONT_SIZE,
  TITLE_LETTER_SPACING,
  TITLE_FONT_WEIGHT,
  TITLE_SHADOW,
} from "./constants";

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  const fadeOut = interpolate(
    frame,
    [CARD_FADE_OUT_START, CARD_FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  const scale = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_END],
    [0.9, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: TITLE_Y,
        left: "50%",
        transform: `translateX(-50%) scale(${scale})`,
        transformOrigin: "center center",
        opacity: fadeIn * fadeOut,
        fontFamily: "'Inter', sans-serif",
        fontWeight: TITLE_FONT_WEIGHT,
        fontSize: TITLE_FONT_SIZE,
        color: TITLE_COLOR,
        letterSpacing: TITLE_LETTER_SPACING,
        textShadow: TITLE_SHADOW,
        textAlign: "center" as const,
        whiteSpace: "nowrap" as const,
      }}
    >
      {TITLE_TEXT}
    </div>
  );
};

export default TitleText;
