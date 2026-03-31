import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  ACCENT_BLUE,
  TEXT_DIM,
  MONO_FONT,
  SANS_FONT,
  ARROW_POS,
  ARROW_START,
  ARROW_FADE_END,
} from "./constants";

export const FlowArrow: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - ARROW_START;
  if (localFrame < 0) return null;

  const fadeDuration = ARROW_FADE_END - ARROW_START;

  const opacity = interpolate(localFrame, [0, fadeDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const scale = interpolate(localFrame, [0, fadeDuration], [0.7, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Subtle pulse on the arrow
  const pulse = interpolate(
    localFrame % 60,
    [0, 30, 60],
    [1, 1.08, 1],
    { extrapolateRight: "clamp" }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: ARROW_POS.x,
        top: ARROW_POS.y,
        width: 40,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        gap: 6,
        opacity,
        transform: `scale(${scale})`,
      }}
    >
      <span
        style={{
          fontFamily: SANS_FONT,
          fontSize: 36,
          color: ACCENT_BLUE,
          lineHeight: 1,
          transform: `scale(${pulse})`,
          display: "inline-block",
        }}
      >
        →
      </span>
      <span
        style={{
          fontFamily: MONO_FONT,
          fontSize: 12,
          color: TEXT_DIM,
          letterSpacing: 0.5,
        }}
      >
        generate
      </span>
    </div>
  );
};

export default FlowArrow;
