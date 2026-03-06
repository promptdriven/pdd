import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile } from "remotion";
import { BlackOverlay } from "./BlackOverlay";
import { BG_COLOR, VIDEO_SRC } from "./constants";

export const defaultColdOpen06FadeBookendsProps = {};

/**
 * Fade-In / Fade-Out Bookends for the cold open section.
 *
 * Renders the cold open Veo footage with a black overlay that:
 * - Fades in from solid black over ~1s (frames 0–30)
 * - Stays fully transparent through the middle
 * - Fades out to solid black over ~1s (frames 440–470)
 */
export const ColdOpen06FadeBookends: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo desk footage layer */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile(VIDEO_SRC)}
          style={{ width: "100%", height: "100%" }}
        />
      </AbsoluteFill>

      {/* Black overlay — topmost layer, handles fade bookends */}
      <BlackOverlay />
    </AbsoluteFill>
  );
};

export default ColdOpen06FadeBookends;
