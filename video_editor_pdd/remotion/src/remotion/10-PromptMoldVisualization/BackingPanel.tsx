import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  PANEL_X,
  PANEL_Y,
  PANEL_W,
  PANEL_H,
  PANEL_RADIUS,
  PANEL_BG,
  PANEL_FADE_START,
  PANEL_FADE_END,
} from "./constants";

export const BackingPanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Only handle panel fade-in; parent handles overall fade-out
  const opacity = interpolate(
    frame,
    [PANEL_FADE_START, PANEL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: PANEL_X,
        top: PANEL_Y,
        width: PANEL_W,
        height: PANEL_H,
        borderRadius: PANEL_RADIUS,
        backgroundColor: PANEL_BG,
        backdropFilter: "blur(10px)",
        WebkitBackdropFilter: "blur(10px)",
        opacity,
      }}
    />
  );
};
