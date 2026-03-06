import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

import {
  BACKDROP_FILL,
  BACKDROP_BLUR,
  BACKDROP_BORDER_COLOR,
  BACKDROP_HEIGHT,
  BACKDROP_FEATHER_PX,
  TRACK_FADE_IN_FRAMES,
  TRACK_FADE_OUT_FRAMES,
  TOTAL_FRAMES,
} from "./constants";

export const SubtitleBackdrop: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in at start, fade out at end
  const opacity = interpolate(
    frame,
    [
      0,
      TRACK_FADE_IN_FRAMES,
      TOTAL_FRAMES - TRACK_FADE_OUT_FRAMES,
      TOTAL_FRAMES,
    ],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <>
      {/* Top feathered edge gradient */}
      <div
        style={{
          position: "absolute",
          bottom: BACKDROP_HEIGHT,
          left: 0,
          width: "100%",
          height: BACKDROP_FEATHER_PX,
          background: `linear-gradient(to bottom, transparent, ${BACKDROP_FILL})`,
          opacity,
        }}
      />
      {/* Main backdrop band */}
      <div
        style={{
          position: "absolute",
          bottom: 0,
          left: 0,
          width: "100%",
          height: BACKDROP_HEIGHT,
          backgroundColor: BACKDROP_FILL,
          backdropFilter: `blur(${BACKDROP_BLUR}px)`,
          WebkitBackdropFilter: `blur(${BACKDROP_BLUR}px)`,
          borderTop: `1px solid ${BACKDROP_BORDER_COLOR}`,
          opacity,
        }}
      />
    </>
  );
};

export default SubtitleBackdrop;
