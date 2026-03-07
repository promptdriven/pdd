import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

import {
  BACKDROP_FILL,
  BACKDROP_BLUR,
  BACKDROP_HEIGHT,
  BACKDROP_Y_START,
  BACKDROP_FEATHER_PX,
  TRACK_FADE_IN_FRAMES,
  TOTAL_FRAMES,
  FADE_OUT_START_BEFORE_END,
  FADE_OUT_END_BEFORE_END,
} from "./constants";

export const SubtitleBackdrop: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in: 0→1 over first 15 frames (easeInOutCubic)
  const fadeInProgress = interpolate(
    frame,
    [0, TRACK_FADE_IN_FRAMES],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const fadeIn = Easing.inOut(Easing.cubic)(fadeInProgress);

  // Fade out: 1→0 from (end-60) to (end-15) — gives CTA clean space
  const fadeOutStart = TOTAL_FRAMES - FADE_OUT_START_BEFORE_END;
  const fadeOutEnd = TOTAL_FRAMES - FADE_OUT_END_BEFORE_END;
  const fadeOutProgress = interpolate(
    frame,
    [fadeOutStart, fadeOutEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const fadeOut = 1 - Easing.in(Easing.cubic)(fadeOutProgress);

  // Combine: min of fadeIn and fadeOut
  const opacity = Math.min(fadeIn, fadeOut);

  return (
    <>
      {/* Top feathered edge gradient */}
      <div
        style={{
          position: "absolute",
          top: BACKDROP_Y_START - BACKDROP_FEATHER_PX,
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
          top: BACKDROP_Y_START,
          left: 0,
          width: "100%",
          height: BACKDROP_HEIGHT,
          backgroundColor: BACKDROP_FILL,
          backdropFilter: `blur(${BACKDROP_BLUR}px)`,
          WebkitBackdropFilter: `blur(${BACKDROP_BLUR}px)`,
          opacity,
        }}
      />
      {/* Bottom feathered edge gradient */}
      <div
        style={{
          position: "absolute",
          top: BACKDROP_Y_START + BACKDROP_HEIGHT,
          left: 0,
          width: "100%",
          height: BACKDROP_FEATHER_PX,
          background: `linear-gradient(to top, transparent, ${BACKDROP_FILL})`,
          opacity,
        }}
      />
    </>
  );
};

export default SubtitleBackdrop;
