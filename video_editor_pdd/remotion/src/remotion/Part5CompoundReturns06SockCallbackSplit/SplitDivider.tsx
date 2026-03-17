import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_H,
  SPLIT_X,
  SPLIT_LINE_W,
  SPLIT_LINE_COLOR,
  SPLIT_LINE_OPACITY,
  SPLIT_LINE_DRAW_START,
  SPLIT_LINE_DRAW_DUR,
  REALIZATION_FLASH_START,
  GLOW_LINE_COLOR,
  GLOW_LINE_PEAK_OPACITY,
} from "./constants";

export const SplitDivider: React.FC = () => {
  const frame = useCurrentFrame();

  // Vertical draw animation: scaleY from 0→1
  const drawProgress = interpolate(
    frame,
    [SPLIT_LINE_DRAW_START, SPLIT_LINE_DRAW_START + SPLIT_LINE_DRAW_DUR],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.bezier(0.33, 1, 0.68, 1)) }
  );

  // Glow effect during realization moment
  const glowOpacity = interpolate(
    frame,
    [
      REALIZATION_FLASH_START,
      REALIZATION_FLASH_START + 5,
      REALIZATION_FLASH_START + 10,
    ],
    [0, GLOW_LINE_PEAK_OPACITY, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  return (
    <>
      {/* Main split line */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X - SPLIT_LINE_W / 2,
          top: 0,
          width: SPLIT_LINE_W,
          height: CANVAS_H,
          backgroundColor: SPLIT_LINE_COLOR,
          opacity: SPLIT_LINE_OPACITY * drawProgress,
          transformOrigin: "top center",
          transform: `scaleY(${drawProgress})`,
        }}
      />

      {/* Glow line during realization */}
      {glowOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: SPLIT_X - 3,
            top: 0,
            width: 6,
            height: CANVAS_H,
            backgroundColor: GLOW_LINE_COLOR,
            opacity: glowOpacity,
            filter: "blur(3px)",
          }}
        />
      )}
    </>
  );
};

export default SplitDivider;
