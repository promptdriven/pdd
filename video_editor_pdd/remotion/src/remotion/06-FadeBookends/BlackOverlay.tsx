import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame } from "remotion";
import {
  FADE_IN_START,
  FADE_IN_END,
  FADE_OUT_START,
  FADE_OUT_END,
  OVERLAY_COLOR,
  OVERLAY_Z_INDEX,
} from "./constants";

/**
 * Full-screen black overlay that handles fade-in and fade-out bookends.
 * Renders on top of all other layers (z-index topmost).
 *
 * - Fade-in: opacity 1 → 0 over frames 0–30 (easeOutQuad)
 * - Fade-out: opacity 0 → 1 over frames 440–470 (easeInQuad)
 * - Between fades: overlay is not rendered at all.
 */
export const BlackOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  const showFadeIn = frame <= FADE_IN_END;
  const showFadeOut = frame >= FADE_OUT_START;

  // Between fades — no overlay needed
  if (!showFadeIn && !showFadeOut) {
    return null;
  }

  let opacity: number;

  if (showFadeIn) {
    // Fade-in: screen starts black, reveals content underneath
    opacity = interpolate(frame, [FADE_IN_START, FADE_IN_END], [1, 0], {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });
  } else {
    // Fade-out: content darkens back to black
    opacity = interpolate(frame, [FADE_OUT_START, FADE_OUT_END], [0, 1], {
      easing: Easing.in(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });
  }

  return (
    <AbsoluteFill
      style={{
        zIndex: OVERLAY_Z_INDEX,
        backgroundColor: OVERLAY_COLOR,
        opacity,
      }}
    />
  );
};

export default BlackOverlay;
