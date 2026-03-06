import React from "react";
import { AbsoluteFill } from "remotion";
import {
  TEXT_CENTER_X,
  TEXT_CENTER_Y,
  GLOW_RADIUS,
  GLOW_COLOR,
} from "./constants";

export const RadialGlow: React.FC<{ opacity: number }> = ({ opacity }) => {
  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(circle ${GLOW_RADIUS}px at ${TEXT_CENTER_X}px ${TEXT_CENTER_Y}px, ${GLOW_COLOR} 0%, transparent 70%)`,
        opacity,
      }}
    />
  );
};

export default RadialGlow;
