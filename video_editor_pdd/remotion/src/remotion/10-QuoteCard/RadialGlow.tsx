import React from "react";
import { AbsoluteFill } from "remotion";
import {
  CANVAS_CENTER_X,
  TEXT_CLUSTER_Y,
  GLOW_COLOR,
  GLOW_RADIUS,
} from "./constants";

export const RadialGlow: React.FC<{ opacity: number }> = ({ opacity }) => {
  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(circle ${GLOW_RADIUS}px at ${CANVAS_CENTER_X}px ${TEXT_CLUSTER_Y}px, ${GLOW_COLOR} 0%, transparent 70%)`,
        opacity,
      }}
    />
  );
};
