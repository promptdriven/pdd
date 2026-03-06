import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  URL_FADE_START,
  URL_FADE_END,
  GLOW_PULSE_CYCLE,
  URL_TEXT,
  URL_FONT_SIZE,
  URL_FONT_WEIGHT,
  URL_LETTER_SPACING,
  BRAND_BLUE,
  TEXT_SHADOW,
} from "./constants";

export const UrlLink: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [URL_FADE_START, URL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Blue glow pulse after fully visible
  const glowIntensity =
    frame >= URL_FADE_END
      ? interpolate(
          Math.sin(((frame - URL_FADE_END) / GLOW_PULSE_CYCLE) * Math.PI * 2),
          [-1, 1],
          [0.3, 0.7],
        )
      : 0.3;

  return (
    <div
      style={{
        opacity,
        fontFamily: "Inter, sans-serif",
        fontSize: URL_FONT_SIZE,
        fontWeight: URL_FONT_WEIGHT,
        letterSpacing: URL_LETTER_SPACING,
        color: BRAND_BLUE,
        textShadow: `${TEXT_SHADOW}, 0 0 20px rgba(59, 130, 246, ${glowIntensity})`,
        textAlign: "center",
      }}
    >
      <span
        style={{
          borderBottom: `2px solid rgba(59, 130, 246, 0.4)`,
          paddingBottom: 2,
        }}
      >
        {URL_TEXT}
      </span>
    </div>
  );
};
