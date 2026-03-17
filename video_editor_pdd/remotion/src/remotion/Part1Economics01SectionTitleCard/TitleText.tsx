import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TITLE_TEXT,
  TITLE_FADE_START,
  TITLE_FADE_END,
  TITLE_SLIDE_PX,
  TITLE_Y,
  AMBER_ACCENT,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_OPACITY,
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
      easing: Easing.out(Easing.cubic),
    }
  );

  const translateY = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_END],
    [TITLE_SLIDE_PX, 0],
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
        top: TITLE_Y,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        opacity: fadeIn * TITLE_OPACITY,
        transform: `translateY(${translateY}px)`,
        fontFamily: "'Inter', sans-serif",
        fontWeight: TITLE_FONT_WEIGHT,
        fontSize: TITLE_FONT_SIZE,
        color: AMBER_ACCENT,
        textAlign: "center" as const,
        whiteSpace: "nowrap" as const,
      }}
    >
      {TITLE_TEXT}
    </div>
  );
};

export default TitleText;
