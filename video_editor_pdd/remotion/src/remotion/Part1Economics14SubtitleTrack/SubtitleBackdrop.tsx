import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

import {
  BACKDROP_FILL,
  BACKDROP_BLUR,
  BACKDROP_HEIGHT,
  BACKDROP_Y_START,
  BACKDROP_FEATHER_PX,
  TRACK_FADE_IN_FRAMES,
  TRACK_FADE_OUT_FRAMES,
  TOTAL_FRAMES,
  SUBTITLE_START_FRAME,
} from "./constants";

export const SubtitleBackdrop: React.FC = () => {
  const frame = useCurrentFrame();

  // Duration within the Sequence (which starts at SUBTITLE_START_FRAME)
  const subtitleDuration = TOTAL_FRAMES - SUBTITLE_START_FRAME;

  // Fade in at start, fade out at end
  const opacity = interpolate(
    frame,
    [
      0,
      TRACK_FADE_IN_FRAMES,
      subtitleDuration - TRACK_FADE_OUT_FRAMES,
      subtitleDuration,
    ],
    [0, 0.55, 0.55, 0],
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
