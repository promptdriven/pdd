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
} from "./part1Constants";

export const Part1TitleText: React.FC = () => {
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
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        opacity: fadeIn * fadeOut,
      }}
    >
      <div
        style={{
          transform: `scale(${scale})`,
          transformOrigin: "center center",
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
    </div>
  );
};

export default Part1TitleText;
