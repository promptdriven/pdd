import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_CENTER_X,
  RULE_Y,
  RULE_MAX_WIDTH,
  RULE_HEIGHT,
  RULE_EXPAND_START,
  RULE_EXPAND_END,
  FADE_OUT_START,
  FADE_OUT_END,
  ACCENT_GREEN,
} from "./constants";

export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [RULE_EXPAND_START, RULE_EXPAND_END],
    [0, RULE_MAX_WIDTH],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: RULE_Y,
        left: CANVAS_CENTER_X,
        transform: "translateX(-50%)",
        width,
        height: RULE_HEIGHT,
        backgroundColor: ACCENT_GREEN,
        opacity: 0.5 * fadeOut,
        borderRadius: 1,
      }}
    />
  );
};
