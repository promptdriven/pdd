import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  RULE_EXPAND_START,
  RULE_EXPAND_END,
  CARD_FADE_OUT_START,
  CARD_FADE_OUT_END,
  RULE_Y,
  RULE_MAX_WIDTH,
  RULE_HEIGHT,
  RULE_COLOR,
  RULE_OPACITY,
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
      easing: Easing.inOut(Easing.quad),
    }
  );

  const fadeOut = interpolate(
    frame,
    [CARD_FADE_OUT_START, CARD_FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: RULE_Y,
        left: "50%",
        transform: "translateX(-50%)",
        width,
        height: RULE_HEIGHT,
        backgroundColor: RULE_COLOR,
        opacity: RULE_OPACITY * fadeOut,
      }}
    />
  );
};

export default HorizontalRule;
