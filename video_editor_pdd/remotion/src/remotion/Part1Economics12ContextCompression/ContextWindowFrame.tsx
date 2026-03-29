// ContextWindowFrame.tsx — The fixed-size context window outline with glow and label
import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

import {
  WINDOW_LEFT,
  WINDOW_TOP,
  WINDOW_WIDTH,
  WINDOW_HEIGHT,
  WINDOW_BORDER_RADIUS,
  WINDOW_BORDER_WIDTH,
  WINDOW_BORDER_COLOR,
  WINDOW_GLOW_COLOR,
  PHASE_WINDOW_DRAW_START,
  PHASE_WINDOW_DRAW_END,
  PHASE_LABEL_COLOR,
} from "./constants";

const ContextWindowFrame: React.FC = () => {
  const frame = useCurrentFrame();
  const drawDuration = PHASE_WINDOW_DRAW_END - PHASE_WINDOW_DRAW_START;

  // Animate the border drawing in (via opacity + scale)
  const drawProgress = interpolate(frame, [0, drawDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const borderOpacity = drawProgress;
  const scaleY = interpolate(drawProgress, [0, 1], [0.9, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Label fade-in slightly after frame draws
  const labelOpacity = interpolate(frame, [30, 55], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <>
      {/* Window frame */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT,
          top: WINDOW_TOP,
          width: WINDOW_WIDTH,
          height: WINDOW_HEIGHT,
          border: `${WINDOW_BORDER_WIDTH}px solid ${WINDOW_BORDER_COLOR}`,
          borderRadius: WINDOW_BORDER_RADIUS,
          boxShadow: `0 0 8px ${WINDOW_GLOW_COLOR}`,
          opacity: borderOpacity,
          transform: `scaleY(${scaleY})`,
          transformOrigin: "top center",
          overflow: "hidden",
        }}
      />

      {/* "Context Window" label above */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_LEFT,
          top: WINDOW_TOP - 40,
          width: WINDOW_WIDTH,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontWeight: 600,
          color: PHASE_LABEL_COLOR,
          opacity: labelOpacity,
          letterSpacing: 1,
          textTransform: "uppercase",
        }}
      >
        Context Window
      </div>
    </>
  );
};

export default ContextWindowFrame;
