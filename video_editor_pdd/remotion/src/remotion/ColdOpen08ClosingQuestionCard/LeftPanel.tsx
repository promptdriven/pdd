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
} from "./constants";

export const LeftPanel: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [PANEL_FADE_START, PANEL_FADE_END],
    [0, 1],
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

  // Generate code-line texture pattern
  const lineCount = Math.floor(CANVAS_HEIGHT / CODE_LINE_INTERVAL);
  const lines = Array.from({ length: lineCount }, (_, i) => i * CODE_LINE_INTERVAL);

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
      {/* Subtle code-line texture */}
      {lines.map((y) => (
        <div
          key={y}
          style={{
            position: "absolute",
            left: 0,
            top: y,
            width: "100%",
            height: 1,
            backgroundColor: CODE_LINE_COLOR,
          }}
        />
      ))}
    </div>
  );
};

export default LeftPanel;
