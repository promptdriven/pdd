import React from "react";
import {
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

const WINDOW_WIDTH = 500;
const WINDOW_HEIGHT = 700;
const WINDOW_CENTER_X = 960;
const WINDOW_CENTER_Y = 480;
const WINDOW_LEFT = WINDOW_CENTER_X - WINDOW_WIDTH / 2;
const WINDOW_TOP = WINDOW_CENTER_Y - WINDOW_HEIGHT / 2;
const WINDOW_BORDER_COLOR = "#4A90D9";
const WINDOW_BORDER_RADIUS = 8;
const WINDOW_GLOW_BLUR = 8;
const FRAME_WINDOW_DRAW_END = 60;

/**
 * Animated context-window rectangle that draws in from frame 0→60.
 * Uses a stroke-dashoffset trick to animate the border drawing.
 */
export const ContextWindowFrame: React.FC = () => {
  const frame = useCurrentFrame();

  // Draw progress 0→1 over first 60 frames
  const drawProgress = interpolate(frame, [0, FRAME_WINDOW_DRAW_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const opacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Perimeter for dash animation
  const perimeter = 2 * (WINDOW_WIDTH + WINDOW_HEIGHT);
  const dashOffset = perimeter * (1 - drawProgress);

  return (
    <div
      style={{
        position: "absolute",
        left: WINDOW_LEFT,
        top: WINDOW_TOP,
        width: WINDOW_WIDTH,
        height: WINDOW_HEIGHT,
        opacity,
      }}
    >
      {/* Glow */}
      <div
        style={{
          position: "absolute",
          inset: -WINDOW_GLOW_BLUR,
          borderRadius: WINDOW_BORDER_RADIUS + WINDOW_GLOW_BLUR,
          boxShadow: `0 0 ${WINDOW_GLOW_BLUR}px rgba(74,144,217,0.1)`,
          pointerEvents: "none",
        }}
      />

      {/* SVG border draw-in */}
      <svg
        width={WINDOW_WIDTH}
        height={WINDOW_HEIGHT}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <rect
          x={1}
          y={1}
          width={WINDOW_WIDTH - 2}
          height={WINDOW_HEIGHT - 2}
          rx={WINDOW_BORDER_RADIUS}
          ry={WINDOW_BORDER_RADIUS}
          fill="none"
          stroke={WINDOW_BORDER_COLOR}
          strokeWidth={2}
          strokeDasharray={perimeter}
          strokeDashoffset={dashOffset}
        />
      </svg>

      {/* "Context Window" label above */}
      <div
        style={{
          position: "absolute",
          top: -36,
          left: 0,
          width: WINDOW_WIDTH,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontWeight: 600,
          color: WINDOW_BORDER_COLOR,
          opacity: interpolate(frame, [30, 60], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
          letterSpacing: 1,
          textTransform: "uppercase",
        }}
      >
        Context Window
      </div>
    </div>
  );
};

export default ContextWindowFrame;
