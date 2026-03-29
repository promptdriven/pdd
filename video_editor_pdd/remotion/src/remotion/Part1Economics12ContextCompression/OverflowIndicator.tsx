// OverflowIndicator.tsx — Red dashed line + overflow count label
import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

import {
  OVERFLOW_RED,
  OVERFLOW_GLOW,
  WINDOW_LEFT,
  WINDOW_TOP,
  WINDOW_WIDTH,
  WINDOW_HEIGHT,
  WINDOW_BORDER_WIDTH,
  OVERFLOW_COUNT,
  PHASE_OVERFLOW_HOLD_START,
  PHASE_COMPRESS_START,
} from "./constants";

const DASHED_Y = WINDOW_TOP + WINDOW_HEIGHT;

const OverflowIndicator: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in at frame 300 over 20 frames
  const fadeIn = interpolate(
    frame,
    [PHASE_OVERFLOW_HOLD_START, PHASE_OVERFLOW_HOLD_START + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Fade out as compression begins
  const fadeOut = interpolate(
    frame,
    [PHASE_COMPRESS_START, PHASE_COMPRESS_START + 40],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  const opacity = fadeIn * fadeOut;

  if (opacity <= 0) return null;

  return (
    <>
      {/* Red dashed line at window bottom */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT + WINDOW_BORDER_WIDTH,
          top: DASHED_Y - 2,
          width: WINDOW_WIDTH - WINDOW_BORDER_WIDTH * 2,
          height: 0,
          borderTop: `1.5px dashed ${OVERFLOW_RED}`,
          opacity,
        }}
      />

      {/* Red glow below window */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT,
          top: DASHED_Y,
          width: WINDOW_WIDTH,
          height: 40,
          background: `linear-gradient(to bottom, ${OVERFLOW_GLOW}, transparent)`,
          opacity,
        }}
      />

      {/* Count label */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT,
          top: DASHED_Y + 12,
          width: WINDOW_WIDTH,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 400,
          color: OVERFLOW_RED,
          opacity,
        }}
      >
        {OVERFLOW_COUNT} modules can&apos;t be seen
      </div>
    </>
  );
};

export default OverflowIndicator;
