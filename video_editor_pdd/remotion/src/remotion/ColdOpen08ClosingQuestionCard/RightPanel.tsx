import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  RIGHT_PANEL_COLOR,
  GLOW_COLOR,
  CANVAS_HEIGHT,
  SPLIT_X,
  CANVAS_WIDTH,
  PANEL_FADE_START,
  PANEL_FADE_END,
  FADE_OUT_START,
  FADE_OUT_END,
  MIN_INITIAL_OPACITY,
} from "./constants";

export const RightPanel: React.FC = () => {
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
  const panelWidth = CANVAS_WIDTH - SPLIT_X;

  return (
    <div
      style={{
        position: "absolute",
        right: 0,
        top: 0,
        width: panelWidth,
        height: CANVAS_HEIGHT,
        backgroundColor: RIGHT_PANEL_COLOR,
        opacity,
        overflow: "hidden",
      }}
    >
      {/* Radial glow from center-right at 5% opacity */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          background: `radial-gradient(ellipse at 50% 50%, ${GLOW_COLOR}0D 0%, transparent 70%)`,
        }}
      />
    </div>
  );
};

export default RightPanel;
