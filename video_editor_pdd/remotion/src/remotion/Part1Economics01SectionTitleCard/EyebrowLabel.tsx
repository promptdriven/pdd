import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PART_LABEL,
  LABEL_FADE_START,
  LABEL_FADE_END,
  LABEL_SLIDE_PX,
  LABEL_Y,
  SLATE_TEXT,
  LABEL_FONT_SIZE,
  LABEL_LETTER_SPACING,
  LABEL_FONT_WEIGHT,
  LABEL_OPACITY,
} from "./constants";

export const EyebrowLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const translateY = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_END],
    [LABEL_SLIDE_PX, 0],
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
        top: LABEL_Y,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        opacity: fadeIn * LABEL_OPACITY,
        transform: `translateY(${translateY}px)`,
        fontFamily: "'Inter', sans-serif",
        fontWeight: LABEL_FONT_WEIGHT,
        fontSize: LABEL_FONT_SIZE,
        color: SLATE_TEXT,
        letterSpacing: LABEL_LETTER_SPACING,
        textTransform: "uppercase" as const,
        textAlign: "center" as const,
      }}
    >
      {PART_LABEL}
    </div>
  );
};

export default EyebrowLabel;
