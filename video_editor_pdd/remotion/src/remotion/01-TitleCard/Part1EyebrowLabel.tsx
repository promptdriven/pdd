import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  EYEBROW_TEXT,
  EYEBROW_FADE_START,
  EYEBROW_FADE_END,
  CARD_FADE_OUT_START,
  CARD_FADE_OUT_END,
  EYEBROW_Y,
  ACCENT_BLUE,
  EYEBROW_FONT_SIZE,
  EYEBROW_LETTER_SPACING,
  EYEBROW_FONT_WEIGHT,
  TITLE_SHADOW,
} from "./part1Constants";

export const Part1EyebrowLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [EYEBROW_FADE_START, EYEBROW_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
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

  const translateY = interpolate(
    frame,
    [EYEBROW_FADE_START, EYEBROW_FADE_END],
    [20, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: EYEBROW_Y,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        opacity: fadeIn * fadeOut,
        transform: `translateY(${translateY}px)`,
        fontFamily: "'Inter', sans-serif",
        fontWeight: EYEBROW_FONT_WEIGHT,
        fontSize: EYEBROW_FONT_SIZE,
        color: ACCENT_BLUE,
        letterSpacing: EYEBROW_LETTER_SPACING,
        textTransform: "uppercase" as const,
        textShadow: TITLE_SHADOW,
        textAlign: "center" as const,
      }}
    >
      {EYEBROW_TEXT}
    </div>
  );
};

export default Part1EyebrowLabel;
