import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  LINE_DRAW_START,
  LINE_DRAW_END,
  LINE_COLOR,
  LINE_OPACITY,
  LINE_WIDTH_PX,
  LINE_Y,
  LINE_CENTER_X,
} from "./constants";

/**
 * A thin horizontal accent line that draws from center outward
 * beneath the question text (frames 75-90).
 */
export const AccentLine: React.FC = () => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [LINE_DRAW_START, LINE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.ease),
    }
  );

  const currentHalfWidth = (LINE_WIDTH_PX / 2) * progress;

  if (progress <= 0) return null;

  return (
    <AbsoluteFill>
      <div
        style={{
          position: "absolute",
          top: LINE_Y,
          left: LINE_CENTER_X - currentHalfWidth,
          width: currentHalfWidth * 2,
          height: 1,
          backgroundColor: LINE_COLOR,
          opacity: LINE_OPACITY,
        }}
      />
    </AbsoluteFill>
  );
};
