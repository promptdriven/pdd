import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { COLORS } from "./constants";

/**
 * A subtle circular glow behind each step that lights up when active.
 */
export const StepCircle: React.FC<{
  x: number;
  y: number;
  startFrame: number;
}> = ({ x, y, startFrame }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  // Dim circle is always visible from frame 0
  const baseOpacity = 0.08;

  // Light-up glow
  const glowOpacity = localFrame < 0
    ? 0
    : interpolate(localFrame, [0, 15], [0, 0.15], {
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      });

  return (
    <div
      style={{
        position: "absolute",
        left: x - 45,
        top: y - 45,
        width: 90,
        height: 90,
        borderRadius: "50%",
        backgroundColor: COLORS.blue,
        opacity: baseOpacity + glowOpacity,
      }}
    />
  );
};
