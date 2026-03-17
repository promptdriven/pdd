import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  RULE_DRAW_START,
  RULE_DRAW_END,
  RULE_Y,
  RULE_MAX_WIDTH,
  RULE_HEIGHT,
  AMBER_ACCENT,
  RULE_OPACITY,
} from "./constants";

export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [RULE_DRAW_START, RULE_DRAW_END],
    [0, RULE_MAX_WIDTH],
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
        top: RULE_Y,
        left: "50%",
        transform: "translateX(-50%)",
        width,
        height: RULE_HEIGHT,
        backgroundColor: AMBER_ACCENT,
        opacity: RULE_OPACITY,
      }}
    />
  );
};

export default HorizontalRule;
