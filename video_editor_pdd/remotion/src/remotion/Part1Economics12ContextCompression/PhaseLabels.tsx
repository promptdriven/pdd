import React from "react";
import {
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

// Inline constants
const WINDOW_CENTER_X = 960;
const WINDOW_CENTER_Y = 480;
const WINDOW_HEIGHT = 700;
const WINDOW_BOTTOM = WINDOW_CENTER_Y - WINDOW_HEIGHT / 2 + WINDOW_HEIGHT;

const LABEL_COLOR = "#E2E8F0";
const RATIO_COLOR = "#5AAA6E";

const FRAME_OVERFLOW_APPEAR = 300;
const FRAME_COMPRESS_START = 420;
const FRAME_RESULT_APPEAR = 600;

/**
 * Phase labels that appear at key moments:
 * - "20 modules as code — doesn't fit" (Phase 1)
 * - "Same system. 5-10× more fits." (Phase 2)
 */
export const PhaseLabels: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1 label: appears at frame 300, fades out at frame 420
  const phase1In = interpolate(
    frame,
    [FRAME_OVERFLOW_APPEAR, FRAME_OVERFLOW_APPEAR + 25],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const phase1Out = interpolate(
    frame,
    [FRAME_COMPRESS_START, FRAME_COMPRESS_START + 30],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const phase1Opacity = phase1In * phase1Out;

  // Phase 2 label: appears at frame 600 with easeOut(back) overshoot
  const phase2Progress = interpolate(
    frame,
    [FRAME_RESULT_APPEAR, FRAME_RESULT_APPEAR + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.4)) }
  );
  const phase2Opacity = interpolate(
    frame,
    [FRAME_RESULT_APPEAR, FRAME_RESULT_APPEAR + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div style={{ position: "absolute", inset: 0, pointerEvents: "none" }}>
      {/* Phase 1: "20 modules as code — doesn't fit" */}
      {phase1Opacity > 0.001 && (
        <div
          style={{
            position: "absolute",
            left: 0,
            top: WINDOW_BOTTOM + 60,
            width: 1920,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 18,
            fontWeight: 700,
            color: LABEL_COLOR,
            opacity: phase1Opacity,
          }}
        >
          20 modules as code — doesn&apos;t fit.
        </div>
      )}

      {/* Phase 2: "Same system. 5-10× more fits." */}
      {phase2Opacity > 0.001 && (
        <div
          style={{
            position: "absolute",
            left: 0,
            top: WINDOW_BOTTOM + 60,
            width: 1920,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 20,
            fontWeight: 700,
            color: RATIO_COLOR,
            opacity: phase2Opacity,
            transform: `scale(${interpolate(phase2Progress, [0, 1], [0.85, 1])})`,
          }}
        >
          Same system. 5-10× more fits.
        </div>
      )}
    </div>
  );
};

export default PhaseLabels;
