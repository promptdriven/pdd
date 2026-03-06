import React from "react";
import { AbsoluteFill } from "remotion";
import {
  GLOW_CENTER_X,
  GLOW_CENTER_Y,
  GLOW_RADIUS,
  ACCENT_GREEN,
  ACCENT_GOLD,
  ACCENT_PURPLE,
} from "./constants";

export const TricolorGlow: React.FC<{ opacity: number }> = ({ opacity }) => {
  return (
    <AbsoluteFill
      style={{
        background: [
          `radial-gradient(circle ${GLOW_RADIUS * 0.6}px at ${GLOW_CENTER_X - 120}px ${GLOW_CENTER_Y}px, ${ACCENT_GREEN}22 0%, transparent 70%)`,
          `radial-gradient(circle ${GLOW_RADIUS * 0.6}px at ${GLOW_CENTER_X}px ${GLOW_CENTER_Y}px, ${ACCENT_GOLD}22 0%, transparent 70%)`,
          `radial-gradient(circle ${GLOW_RADIUS * 0.6}px at ${GLOW_CENTER_X + 120}px ${GLOW_CENTER_Y}px, ${ACCENT_PURPLE}22 0%, transparent 70%)`,
        ].join(", "),
        opacity: opacity * 0.4,
      }}
    />
  );
};

export default TricolorGlow;
