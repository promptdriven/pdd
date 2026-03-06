import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  DIVIDER_X,
  DIVIDER_COLOR,
  DIVIDER_FADE_IN_START,
  DIVIDER_FADE_IN_END,
  PANEL_SLIDE_OUT_START,
  PANEL_SLIDE_OUT_END,
  HEIGHT,
} from "./constants";

export const VerticalDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [DIVIDER_FADE_IN_START, DIVIDER_FADE_IN_END, PANEL_SLIDE_OUT_START, PANEL_SLIDE_OUT_END],
    [0, 0.4, 0.4, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) },
  );

  return (
    <div
      style={{
        position: "absolute",
        left: DIVIDER_X,
        top: 100,
        width: 2,
        height: HEIGHT - 200,
        transform: "translateX(-1px)",
        background: DIVIDER_COLOR,
        opacity,
        boxShadow: `0 0 12px 4px rgba(255, 255, 255, ${opacity * 0.3})`,
      }}
    />
  );
};

export default VerticalDivider;
