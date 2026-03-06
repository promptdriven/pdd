import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PANEL_TOP,
  PANEL_HEIGHT,
  DIVIDER_X,
  DIVIDER_WIDTH,
  DIVIDER_COLOR,
  DIVIDER_FADE_START,
  DIVIDER_FADE_END,
  DISSOLVE_START,
  DISSOLVE_END,
} from "./constants";

export const VerticalDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [DIVIDER_FADE_START, DIVIDER_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const fadeOut = interpolate(
    frame,
    [DISSOLVE_START, DISSOLVE_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );

  const opacity = Math.min(fadeIn, fadeOut);

  return (
    <div
      style={{
        position: "absolute",
        left: DIVIDER_X - DIVIDER_WIDTH / 2,
        top: PANEL_TOP,
        width: DIVIDER_WIDTH,
        height: PANEL_HEIGHT,
        backgroundColor: DIVIDER_COLOR,
        opacity,
        boxShadow: `0 0 12px 4px rgba(255, 255, 255, 0.15), 0 0 24px 8px rgba(255, 255, 255, 0.08)`,
      }}
    />
  );
};

export default VerticalDivider;
