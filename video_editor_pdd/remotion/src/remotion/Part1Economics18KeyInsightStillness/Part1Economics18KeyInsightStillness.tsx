import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { BG_COLOR } from "./constants";
import { HorizontalLine } from "./HorizontalLine";
import { InsightText } from "./InsightText";

/**
 * Section 1.18: Key Insight Stillness — The 3B1B Beat
 *
 * A deliberate moment of stillness: near-black screen with a thin horizontal
 * line drawing outward from center, and quiet text fading in above it.
 * The palate cleanser between the data-heavy economic argument and the
 * synthesis that follows.
 *
 * Duration: 360 frames (12s @ 30fps)
 */

export const defaultPart1Economics18KeyInsightStillnessProps = {};

export const Part1Economics18KeyInsightStillness: React.FC = () => {
  const frame = useCurrentFrame();

  // Background clearing effect: transition from slightly lighter to target bg
  // Frames 0-60: simulate "previous elements fading" by darkening from a
  // marginally lighter near-black to the final deep black
  const bgBrightness = interpolate(frame, [0, 60], [1.15, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.bezier(0.32, 0, 0.67, 0)),
  });

  // A very subtle vignette pulse of clearing — expressed as a dim overlay
  // that fades from slightly visible (#0A0F1A tint) to fully transparent
  const clearOverlayOpacity = interpolate(frame, [0, 60], [0.4, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.bezier(0.32, 0, 0.67, 0)),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
      }}
    >
      {/* Clearing overlay — fades from slight tint to transparent */}
      <AbsoluteFill
        style={{
          backgroundColor: "#0A0F1A",
          opacity: clearOverlayOpacity,
          filter: `brightness(${bgBrightness})`,
        }}
      />

      {/* Thin horizontal line drawing from center */}
      <HorizontalLine />

      {/* Quiet insight text */}
      <InsightText />
    </AbsoluteFill>
  );
};

export default Part1Economics18KeyInsightStillness;
