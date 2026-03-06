import React from "react";
import { AbsoluteFill } from "remotion";
import {
  GLOW_CENTER_X,
  GLOW_CENTER_Y,
  GLOW_COLOR,
  GLOW_RADIUS,
} from "./constants";

export const RadialGlow: React.FC<{ opacity: number }> = ({ opacity }) => {
  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(circle ${GLOW_RADIUS}px at ${GLOW_CENTER_X}px ${GLOW_CENTER_Y}px, ${GLOW_COLOR}, transparent)`,
        opacity: opacity * 0.6,
      }}
    />
  );
};
