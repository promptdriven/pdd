import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  RULE_Y,
  RULE_WIDTH,
  RULE_HEIGHT,
  RULE_COLOR,
  RULE_OPACITY,
  RULE_START_FRAME,
  RULE_DRAW_DURATION,
  RULE_CENTER_X,
} from "./constants";

/**
 * Horizontal rule that draws from center outward.
 * Appears at frame 50, animates width over 10 frames with easeOut(cubic).
 */
export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - RULE_START_FRAME;
  if (localFrame < 0) return null;

  const progress = interpolate(
    localFrame,
    [0, RULE_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const currentWidth = RULE_WIDTH * progress;

  return (
    <div
      style={{
        position: "absolute",
        top: RULE_Y,
        left: RULE_CENTER_X - currentWidth / 2,
        width: currentWidth,
        height: RULE_HEIGHT,
        backgroundColor: RULE_COLOR,
        opacity: RULE_OPACITY,
        pointerEvents: "none",
      }}
    />
  );
};
