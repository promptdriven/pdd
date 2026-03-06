import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  QUOTE_TEXT,
  QUOTE_FADE_IN_START,
  QUOTE_FADE_IN_END,
  FADE_OUT_START,
  FADE_OUT_END,
  TEXT_CENTER_X,
  QUOTE_Y,
  QUOTE_COLOR,
  QUOTE_FONT_SIZE,
  QUOTE_FONT_WEIGHT,
  QUOTE_LETTER_SPACING,
  QUOTE_TEXT_SHADOW,
  QUOTE_SLIDE_DISTANCE,
} from "./constants";

export const QuoteText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [QUOTE_FADE_IN_START, QUOTE_FADE_IN_END, FADE_OUT_START, FADE_OUT_END],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing:
        frame <= QUOTE_FADE_IN_END
          ? Easing.out(Easing.quad)
          : Easing.in(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [QUOTE_FADE_IN_START, QUOTE_FADE_IN_END],
    [QUOTE_SLIDE_DISTANCE, 0],
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
        top: QUOTE_Y,
        left: 0,
        width: "100%",
        display: "flex",
        justifyContent: "center",
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <div
        style={{
          color: QUOTE_COLOR,
          fontSize: QUOTE_FONT_SIZE,
          fontWeight: QUOTE_FONT_WEIGHT,
          fontFamily: "Inter, sans-serif",
          letterSpacing: QUOTE_LETTER_SPACING,
          textAlign: "center",
          textShadow: QUOTE_TEXT_SHADOW,
          lineHeight: 1.2,
          maxWidth: 1200,
          padding: "0 80px",
        }}
      >
        {QUOTE_TEXT}
      </div>
    </div>
  );
};

export default QuoteText;
