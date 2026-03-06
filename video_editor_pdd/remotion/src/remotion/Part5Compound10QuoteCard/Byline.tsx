import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BYLINE_TEXT,
  BYLINE_FADE_IN_START,
  BYLINE_FADE_IN_END,
  FADE_OUT_START,
  FADE_OUT_END,
  BYLINE_Y,
  BYLINE_COLOR,
  BYLINE_FONT_SIZE,
  BYLINE_FONT_WEIGHT,
  BYLINE_LETTER_SPACING,
  BYLINE_MAX_OPACITY,
  BYLINE_SLIDE_DISTANCE,
} from "./constants";

export const Byline: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [BYLINE_FADE_IN_START, BYLINE_FADE_IN_END, FADE_OUT_START, FADE_OUT_END],
    [0, BYLINE_MAX_OPACITY, BYLINE_MAX_OPACITY, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing:
        frame <= BYLINE_FADE_IN_END
          ? Easing.out(Easing.cubic)
          : Easing.in(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [BYLINE_FADE_IN_START, BYLINE_FADE_IN_END],
    [BYLINE_SLIDE_DISTANCE, 0],
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
        top: BYLINE_Y,
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
          color: BYLINE_COLOR,
          fontSize: BYLINE_FONT_SIZE,
          fontWeight: BYLINE_FONT_WEIGHT,
          fontFamily: "Inter, sans-serif",
          fontStyle: "italic",
          letterSpacing: BYLINE_LETTER_SPACING,
          textAlign: "center",
        }}
      >
        {BYLINE_TEXT}
      </div>
    </div>
  );
};

export default Byline;
