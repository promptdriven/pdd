import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  AMBER,
  MOLD_CENTER_X,
  NOZZLE_TOP_Y,
  PROMPT_FILE,
  PHASE_FILE_LABEL_START,
  PHASE_FILE_LABEL_DURATION,
} from "./constants";

export const FileLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const labelEnd = PHASE_FILE_LABEL_START + PHASE_FILE_LABEL_DURATION;

  // Fade in over 15 frames, fade out over 15 frames starting at +30
  const fadeIn = interpolate(
    frame,
    [PHASE_FILE_LABEL_START, PHASE_FILE_LABEL_START + 15],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const fadeOut = interpolate(
    frame,
    [labelEnd - 15, labelEnd],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const opacity = Math.min(fadeIn, fadeOut) * 0.5;

  if (frame < PHASE_FILE_LABEL_START || frame > labelEnd) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: MOLD_CENTER_X + 50,
        top: NOZZLE_TOP_Y - 5,
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 12,
        color: AMBER,
        opacity,
        whiteSpace: "nowrap",
      }}
    >
      {PROMPT_FILE}
    </div>
  );
};
