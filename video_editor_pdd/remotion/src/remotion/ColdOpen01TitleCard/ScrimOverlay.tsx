import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  SCRIM_COLOR,
  SCRIM_MAX_OPACITY,
  FADE_IN_END,
  FADE_OUT_START,
  FADE_OUT_END,
} from "./constants";

export const ScrimOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, FADE_IN_END, FADE_OUT_START, FADE_OUT_END],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing:
        frame <= FADE_IN_END
          ? Easing.out(Easing.cubic)
          : Easing.in(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(ellipse at center, rgba(${SCRIM_COLOR}, ${SCRIM_MAX_OPACITY * opacity}) 0%, rgba(${SCRIM_COLOR}, 0) 70%)`,
      }}
    />
  );
};

export default ScrimOverlay;
