import React from "react";
import { useCurrentFrame, useVideoConfig, interpolate } from "remotion";
import { CANVAS_HEIGHT, SCAN_LINE_COLOR } from "./constants";

/**
 * A subtle 1px horizontal scan line that scrolls from top to bottom,
 * reinforcing the "screen" feeling. Linear easing, very low opacity.
 */
export const ScanLine: React.FC<{ startFrame: number; durationFrames: number }> = ({
  startFrame,
  durationFrames,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const localFrame = frame - startFrame;
  if (localFrame < 0 || localFrame >= durationFrames) return null;

  const y = interpolate(localFrame, [0, durationFrames - 1], [0, CANVAS_HEIGHT], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: y,
        width: "100%",
        height: 1,
        backgroundColor: SCAN_LINE_COLOR,
        opacity: 0.02,
        pointerEvents: "none",
      }}
    />
  );
};

export default ScanLine;
