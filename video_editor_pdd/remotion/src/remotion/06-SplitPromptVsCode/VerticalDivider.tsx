import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  DIVIDER_X,
  DIVIDER_FADE_START,
  DIVIDER_FADE_END,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const VerticalDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [DIVIDER_FADE_START, DIVIDER_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 0.3, 0.3, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: DIVIDER_X - 1,
        top: 80,
        width: 2,
        height: 920,
        backgroundColor: `rgba(255, 255, 255, ${opacity})`,
        boxShadow: `0 0 12px rgba(255, 255, 255, ${opacity * 0.5}), 0 0 24px rgba(255, 255, 255, ${opacity * 0.2})`,
      }}
    />
  );
};

export default VerticalDivider;
