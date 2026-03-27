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
const WINDOW_LEFT = WINDOW_CENTER_X - WINDOW_WIDTH / 2;
const WINDOW_HEIGHT = 700;
const WINDOW_BOTTOM = WINDOW_CENTER_Y - WINDOW_HEIGHT / 2 + WINDOW_HEIGHT;

const OVERFLOW_COLOR = "#EF4444";
const FRAME_OVERFLOW_APPEAR = 300;
const FRAME_COMPRESS_START = 420;

/**
 * Red dashed overflow line and "17 modules can't be seen" label.
 * Fades in at frame 300, fades out as compression begins at frame 420.
 */
export const OverflowIndicator: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in
  const fadeIn = interpolate(
    frame,
    [FRAME_OVERFLOW_APPEAR, FRAME_OVERFLOW_APPEAR + 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Fade out during compression
  const fadeOut = interpolate(
    frame,
    [FRAME_COMPRESS_START, FRAME_COMPRESS_START + 40],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const opacity = fadeIn * fadeOut;
  if (opacity <= 0.001) return null;

  return (
    <div style={{ position: "absolute", inset: 0, pointerEvents: "none", opacity }}>
      {/* Dashed overflow line */}
      <svg
        style={{
          position: "absolute",
          left: WINDOW_LEFT - 20,
          top: WINDOW_BOTTOM - 2,
          width: WINDOW_WIDTH + 40,
          height: 4,
        }}
      >
        <line
          x1={0}
          y1={2}
          x2={WINDOW_WIDTH + 40}
          y2={2}
          stroke={OVERFLOW_COLOR}
          strokeWidth={2}
          strokeDasharray="8 6"
        />
      </svg>

      {/* Red glow below window */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT,
          top: WINDOW_BOTTOM,
          width: WINDOW_WIDTH,
          height: 40,
          background: `linear-gradient(to bottom, rgba(239,68,68,0.12), transparent)`,
          borderRadius: "0 0 8px 8px",
        }}
      />

      {/* Overflow count label */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT,
          top: WINDOW_BOTTOM + 14,
          width: WINDOW_WIDTH,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 400,
          color: OVERFLOW_COLOR,
        }}
      >
        17 modules can&apos;t be seen
      </div>
    </div>
  );
};

export default OverflowIndicator;
