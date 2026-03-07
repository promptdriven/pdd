import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

import {
  BACKDROP_BLUR,
  TRACK_FADE_IN_FRAMES,
  P2_TOTAL_FRAMES,
  P2_BACKDROP_Y_START,
  P2_BACKDROP_HEIGHT,
  P2_BACKDROP_FILL,
  P2_BACKDROP_FEATHER_PX,
  P2_TRACK_FADE_OUT_FRAMES,
} from "./constants";

export const Part2SubtitleBackdrop: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in: 0→1 over first 15 frames (easeInOutCubic)
  const fadeInProgress = interpolate(
    frame,
    [0, TRACK_FADE_IN_FRAMES],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const fadeIn = Easing.inOut(Easing.cubic)(fadeInProgress);

  // Fade out: 1→0 over last 30 frames (easeInOutCubic)
  const fadeOutProgress = interpolate(
    frame,
    [P2_TOTAL_FRAMES - P2_TRACK_FADE_OUT_FRAMES, P2_TOTAL_FRAMES],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const fadeOut = 1 - Easing.inOut(Easing.cubic)(fadeOutProgress);

  const opacity = Math.min(fadeIn, fadeOut);

  return (
    <>
      {/* Top feathered edge gradient */}
      <div
        style={{
          position: "absolute",
          top: P2_BACKDROP_Y_START - P2_BACKDROP_FEATHER_PX,
          left: 0,
          width: "100%",
          height: P2_BACKDROP_FEATHER_PX,
          background: `linear-gradient(to bottom, transparent, ${P2_BACKDROP_FILL})`,
          opacity,
        }}
      />
      {/* Main backdrop band */}
      <div
        style={{
          position: "absolute",
          top: P2_BACKDROP_Y_START,
          left: 0,
          width: "100%",
          height: P2_BACKDROP_HEIGHT,
          backgroundColor: P2_BACKDROP_FILL,
          backdropFilter: `blur(${BACKDROP_BLUR}px)`,
          WebkitBackdropFilter: `blur(${BACKDROP_BLUR}px)`,
          opacity,
        }}
      />
      {/* Bottom feathered edge gradient */}
      <div
        style={{
          position: "absolute",
          top: P2_BACKDROP_Y_START + P2_BACKDROP_HEIGHT,
          left: 0,
          width: "100%",
          height: P2_BACKDROP_FEATHER_PX,
          background: `linear-gradient(to top, transparent, ${P2_BACKDROP_FILL})`,
          opacity,
        }}
      />
    </>
  );
};

export default Part2SubtitleBackdrop;
