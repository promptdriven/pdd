import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  LINE_Y,
  LINE_CENTER_X,
  LINE_HALF_LENGTH,
  LINE_COLOR,
  LINE_OPACITY,
  LINE_WIDTH_PX,
  LINE_DRAW_START,
  LINE_DRAW_END,
} from "./constants";

/**
 * A thin horizontal line that draws outward from center.
 * Appears at frame LINE_DRAW_START and completes at LINE_DRAW_END.
 */
export const HorizontalLine: React.FC = () => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [LINE_DRAW_START, LINE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );

  const currentHalfLength = LINE_HALF_LENGTH * progress;

  return (
    <div
      style={{
        position: "absolute",
        top: LINE_Y,
        left: LINE_CENTER_X - currentHalfLength,
        width: currentHalfLength * 2,
        height: LINE_WIDTH_PX,
        backgroundColor: LINE_COLOR,
        opacity: LINE_OPACITY,
      }}
    />
  );
};

export default HorizontalLine;
