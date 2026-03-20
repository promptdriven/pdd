import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  QUESTION_X,
  QUESTION_Y,
  GLOW_COLOR,
  GLOW_MAX_OPACITY,
  GLOW_RADIUS,
  FADE_IN_END,
  HOLD_END,
  TOTAL_FRAMES,
} from "./constants";

export const AmbientGlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Glow fades in at half the text rate, holds, then fades out with text
  const glowOpacity = interpolate(
    frame,
    [0, FADE_IN_END, HOLD_END, TOTAL_FRAMES],
    [0, GLOW_MAX_OPACITY, GLOW_MAX_OPACITY, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  const diameter = GLOW_RADIUS * 2;

  return (
    <div
      style={{
        position: "absolute",
        left: QUESTION_X - GLOW_RADIUS,
        top: QUESTION_Y - GLOW_RADIUS,
        width: diameter,
        height: diameter,
        borderRadius: "50%",
        background: `radial-gradient(circle, ${GLOW_COLOR} 0%, transparent 70%)`,
        opacity: glowOpacity,
        pointerEvents: "none",
      }}
    />
  );
};

export default AmbientGlow;
