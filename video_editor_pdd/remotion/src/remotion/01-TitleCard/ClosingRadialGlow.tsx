import React from "react";
import { AbsoluteFill } from "remotion";
import {
  GLOW1_CENTER_X,
  GLOW1_CENTER_Y,
  GLOW1_RADIUS,
  GLOW1_COLOR,
  GLOW2_CENTER_X,
  GLOW2_CENTER_Y,
  GLOW2_RADIUS,
  GLOW2_COLOR,
} from "./closingConstants";

export const ClosingRadialGlow: React.FC<{ opacity: number }> = ({
  opacity,
}) => {
  return (
    <>
      <AbsoluteFill
        style={{
          background: `radial-gradient(circle ${GLOW1_RADIUS}px at ${GLOW1_CENTER_X}px ${GLOW1_CENTER_Y}px, ${GLOW1_COLOR}, transparent)`,
          opacity: opacity * 0.5,
        }}
      />
      <AbsoluteFill
        style={{
          background: `radial-gradient(circle ${GLOW2_RADIUS}px at ${GLOW2_CENTER_X}px ${GLOW2_CENTER_Y}px, ${GLOW2_COLOR}, transparent)`,
          opacity: opacity * 0.4,
        }}
      />
    </>
  );
};

export default ClosingRadialGlow;
