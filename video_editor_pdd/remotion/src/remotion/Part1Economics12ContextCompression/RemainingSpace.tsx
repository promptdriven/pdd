import React from "react";
import {
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

// Inline constants
const WINDOW_WIDTH = 500;
const WINDOW_CENTER_X = 960;
const WINDOW_CENTER_Y = 480;
const WINDOW_HEIGHT = 700;
const WINDOW_LEFT = WINDOW_CENTER_X - WINDOW_WIDTH / 2;
const WINDOW_TOP = WINDOW_CENTER_Y - WINDOW_HEIGHT / 2;

const PROMPT_BLOCK_HEIGHT = 30;
const PROMPT_GAP = 3;
const MODULE_COUNT = 20;
const TOTAL_PROMPT_HEIGHT = MODULE_COUNT * PROMPT_BLOCK_HEIGHT + (MODULE_COUNT - 1) * PROMPT_GAP; // 657

const REMAINING_SPACE_COLOR = "#5AAA6E";

const FRAME_RESULT_APPEAR = 600;

/**
 * Green "remaining space" fill at the bottom of the window after compression.
 * Shows that all 20 prompt blocks fit with room to spare.
 */
export const RemainingSpace: React.FC = () => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [FRAME_RESULT_APPEAR, FRAME_RESULT_APPEAR + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (progress <= 0) return null;

  const spaceHeight = WINDOW_HEIGHT - TOTAL_PROMPT_HEIGHT;
  const fillHeight = spaceHeight * progress;

  return (
    <div style={{ position: "absolute", inset: 0, pointerEvents: "none" }}>
      {/* Green fill at bottom of window */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT,
          top: WINDOW_TOP + WINDOW_HEIGHT - fillHeight,
          width: WINDOW_WIDTH,
          height: fillHeight,
          backgroundColor: "rgba(90,170,110,0.05)",
          borderRadius: "0 0 8px 8px",
        }}
      />

      {/* "Room to spare" label */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT,
          top: WINDOW_TOP + TOTAL_PROMPT_HEIGHT + (spaceHeight / 2) - 8,
          width: WINDOW_WIDTH,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 12,
          fontWeight: 400,
          fontStyle: "italic",
          color: REMAINING_SPACE_COLOR,
          opacity: 0.5 * progress,
        }}
      >
        Room to spare
      </div>
    </div>
  );
};

export default RemainingSpace;
