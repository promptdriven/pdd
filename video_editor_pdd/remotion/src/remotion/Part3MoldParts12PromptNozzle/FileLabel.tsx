import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  NOZZLE_COLOR,
  MOLD_CENTER_X,
  NOZZLE_Y,
  PROMPT_FILE,
  PHASE_FILE_LABEL_START,
  PHASE_FILE_LABEL_END,
} from "./constants";

/**
 * Shows `user_parser.prompt` file label near the nozzle,
 * fading in and then fading out.
 */
export const FileLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [PHASE_FILE_LABEL_START, PHASE_FILE_LABEL_START + 15],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const fadeOut = interpolate(
    frame,
    [PHASE_FILE_LABEL_END - 15, PHASE_FILE_LABEL_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const opacity = Math.min(fadeIn, fadeOut) * 0.5;

  if (frame < PHASE_FILE_LABEL_START || frame > PHASE_FILE_LABEL_END) {
    return null;
  }

  return (
    <div
      style={{
        position: "absolute",
        left: MOLD_CENTER_X + 60,
        top: NOZZLE_Y + 15,
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 12,
        color: NOZZLE_COLOR,
        opacity,
        whiteSpace: "nowrap",
      }}
    >
      {PROMPT_FILE}
    </div>
  );
};
