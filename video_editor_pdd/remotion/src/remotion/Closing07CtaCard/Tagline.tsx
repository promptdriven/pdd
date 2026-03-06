import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TAGLINE_FADE_START,
  TAGLINE_FADE_END,
  TAGLINE_TEXT,
  TAGLINE_FONT_SIZE,
  TAGLINE_FONT_WEIGHT,
  TAGLINE_LETTER_SPACING,
  TITLE_COLOR,
  TEXT_SHADOW,
} from "./constants";

export const Tagline: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TAGLINE_FADE_START, TAGLINE_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [TAGLINE_FADE_START, TAGLINE_FADE_END],
    [10, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        opacity,
        transform: `translateY(${translateY}px)`,
        fontFamily: "Inter, sans-serif",
        fontSize: TAGLINE_FONT_SIZE,
        fontWeight: TAGLINE_FONT_WEIGHT,
        letterSpacing: TAGLINE_LETTER_SPACING,
        color: TITLE_COLOR,
        textShadow: TEXT_SHADOW,
        textAlign: "center",
        marginBottom: 20,
      }}
    >
      {TAGLINE_TEXT}
    </div>
  );
};
