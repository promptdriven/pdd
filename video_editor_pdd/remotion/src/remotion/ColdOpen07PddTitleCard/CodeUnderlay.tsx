import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  CODE_LINES,
  CODE_FONT_FAMILY,
  CODE_FONT_SIZE,
  CODE_COLOR,
  CODE_UNDERLAY_OPACITY_START,
  CODE_UNDERLAY_OPACITY_END,
  CODE_DIM_END_FRAME,
  CANVAS_WIDTH,
} from "./constants";

/**
 * Dimmed code underlay — regenerated code visible at very low opacity.
 * Dims from 0.08 → 0.04 over the first 20 frames, then holds.
 */
export const CodeUnderlay: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, CODE_DIM_END_FRAME],
    [CODE_UNDERLAY_OPACITY_START, CODE_UNDERLAY_OPACITY_END],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: 60,
        left: 120,
        width: CANVAS_WIDTH - 240,
        opacity,
        fontFamily: CODE_FONT_FAMILY,
        fontSize: CODE_FONT_SIZE,
        color: CODE_COLOR,
        lineHeight: 1.6,
        whiteSpace: "pre",
        pointerEvents: "none",
      }}
    >
      {CODE_LINES.map((line, i) => (
        <div key={i}>{line || "\u00A0"}</div>
      ))}
    </div>
  );
};
