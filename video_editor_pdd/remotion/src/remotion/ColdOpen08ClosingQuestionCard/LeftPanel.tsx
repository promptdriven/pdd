import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  LEFT_PANEL_COLOR,
  CODE_LINE_INTERVAL,
  CODE_LINE_COLOR,
  CANVAS_HEIGHT,
  SPLIT_X,
  PANEL_FADE_START,
  PANEL_FADE_END,
  FADE_OUT_START,
  FADE_OUT_END,
  MIN_INITIAL_OPACITY,
} from "./constants";

export const LeftPanel: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [PANEL_FADE_START, PANEL_FADE_END],
    [MIN_INITIAL_OPACITY, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
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

  const opacity = fadeIn * fadeOut;

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: SPLIT_X,
        height: CANVAS_HEIGHT,
        backgroundColor: LEFT_PANEL_COLOR,
        filter: "saturate(0.4)",
        opacity,
        overflow: "hidden",
      }}
    >
      {/* Subtle code-line texture via repeating gradient */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          backgroundImage: `repeating-linear-gradient(
            to bottom,
            ${CODE_LINE_COLOR} 0px,
            ${CODE_LINE_COLOR} 1px,
            transparent 1px,
            transparent ${CODE_LINE_INTERVAL}px
          )`,
        }}
      />
    </div>
  );
};

export default LeftPanel;
