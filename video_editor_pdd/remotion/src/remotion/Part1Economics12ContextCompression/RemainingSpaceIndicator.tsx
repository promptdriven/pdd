// RemainingSpaceIndicator.tsx — Green fill + "Room to spare" label at window bottom
import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

import {
  REMAINING_GREEN,
  REMAINING_GREEN_FILL,
  WINDOW_LEFT,
  WINDOW_TOP,
  WINDOW_WIDTH,
  WINDOW_HEIGHT,
  WINDOW_BORDER_WIDTH,
  MODULE_NAMES,
  PROMPT_BLOCK_HEIGHT,
  PROMPT_BLOCK_GAP,
  PHASE_RESULT_START,
} from "./constants";

const INNER_PADDING = 8;
const TOTAL_PROMPT_HEIGHT =
  MODULE_NAMES.length * PROMPT_BLOCK_HEIGHT +
  (MODULE_NAMES.length - 1) * PROMPT_BLOCK_GAP;
const INNER_HEIGHT = WINDOW_HEIGHT - (WINDOW_BORDER_WIDTH + INNER_PADDING) * 2;
const REMAINING_HEIGHT = INNER_HEIGHT - TOTAL_PROMPT_HEIGHT;
const REMAINING_TOP =
  WINDOW_TOP + WINDOW_BORDER_WIDTH + INNER_PADDING + TOTAL_PROMPT_HEIGHT;

const RemainingSpaceIndicator: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in at frame 600
  const opacity = interpolate(
    frame,
    [PHASE_RESULT_START, PHASE_RESULT_START + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (opacity <= 0 || REMAINING_HEIGHT <= 0) return null;

  return (
    <>
      {/* Green fill area */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT + WINDOW_BORDER_WIDTH + INNER_PADDING,
          top: REMAINING_TOP,
          width: WINDOW_WIDTH - (WINDOW_BORDER_WIDTH + INNER_PADDING) * 2,
          height: REMAINING_HEIGHT,
          backgroundColor: REMAINING_GREEN_FILL,
          borderRadius: 4,
          opacity,
        }}
      />

      {/* "Room to spare" label */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT + WINDOW_BORDER_WIDTH + INNER_PADDING,
          top: REMAINING_TOP + REMAINING_HEIGHT / 2 - 8,
          width: WINDOW_WIDTH - (WINDOW_BORDER_WIDTH + INNER_PADDING) * 2,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 12,
          fontWeight: 400,
          fontStyle: "italic",
          color: REMAINING_GREEN,
          opacity: opacity * 0.5,
        }}
      >
        Room to spare
      </div>
    </>
  );
};

export default RemainingSpaceIndicator;
