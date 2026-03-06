import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  SPLIT_X,
  SPLIT_LINE_WIDTH,
  SPLIT_LINE_COLOR,
  CANVAS_HEIGHT,
  PANEL_FADE_START,
  PANEL_FADE_END,
  FADE_OUT_START,
  FADE_OUT_END,
} from "./constants";

export const SplitLine: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [PANEL_FADE_START, PANEL_FADE_END],
    [0, 1],
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
    }
  );

  const lineHeight = drawProgress * CANVAS_HEIGHT;

  return (
    <div
      style={{
        position: "absolute",
        left: SPLIT_X - SPLIT_LINE_WIDTH / 2,
        top: 0,
        width: SPLIT_LINE_WIDTH,
        height: lineHeight,
        backgroundColor: SPLIT_LINE_COLOR,
        opacity: fadeOut,
      }}
    />
  );
};

export default SplitLine;
