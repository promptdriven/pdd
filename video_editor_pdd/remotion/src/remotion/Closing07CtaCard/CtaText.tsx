import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CTA_FADE_START,
  CTA_FADE_END,
  CTA_TEXT,
  CTA_FONT_SIZE,
  CTA_FONT_WEIGHT,
  CTA_COLOR,
  TEXT_SHADOW,
} from "./constants";

export const CtaText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [CTA_FADE_START, CTA_FADE_END],
    [0, 1],
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
        fontFamily: "Inter, sans-serif",
        fontSize: CTA_FONT_SIZE,
        fontWeight: CTA_FONT_WEIGHT,
        color: CTA_COLOR,
        textShadow: TEXT_SHADOW,
        textAlign: "center",
        marginBottom: 24,
      }}
    >
      {CTA_TEXT}
    </div>
  );
};
