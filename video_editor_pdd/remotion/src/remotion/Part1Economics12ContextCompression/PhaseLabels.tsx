// PhaseLabels.tsx — Animated phase labels: overflow message + result message
import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

import {
  PHASE_LABEL_COLOR,
  OVERFLOW_RED,
  REMAINING_GREEN,
  WINDOW_TOP,
  WINDOW_HEIGHT,
  PHASE_OVERFLOW_HOLD_START,
  PHASE_COMPRESS_START,
  PHASE_RESULT_START,
} from "./constants";

const LABEL_Y = WINDOW_TOP + WINDOW_HEIGHT + 60;

const PhaseLabels: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1 label: "20 modules as code — doesn't fit"
  const phase1FadeIn = interpolate(
    frame,
    [PHASE_OVERFLOW_HOLD_START + 10, PHASE_OVERFLOW_HOLD_START + 35],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );
  const phase1FadeOut = interpolate(
    frame,
    [PHASE_COMPRESS_START, PHASE_COMPRESS_START + 30],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );
  const phase1Opacity = phase1FadeIn * phase1FadeOut;

  // Phase 2 label: "Same system. 5-10× more fits."
  const phase2FadeIn = interpolate(
    frame,
    [PHASE_RESULT_START, PHASE_RESULT_START + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Subtle scale overshoot (back easing effect via spring-like interpolation)
  const phase2Scale = interpolate(
    frame,
    [PHASE_RESULT_START, PHASE_RESULT_START + 20, PHASE_RESULT_START + 35],
    [0.85, 1.04, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <>
      {/* Phase 1: overflow label */}
      {phase1Opacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: 0,
            top: LABEL_Y,
            width: 1920,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 18,
            fontWeight: 700,
            color: PHASE_LABEL_COLOR,
            opacity: phase1Opacity,
          }}
        >
          20 modules as code —{" "}
          <span style={{ color: OVERFLOW_RED }}>doesn&apos;t fit</span>
        </div>
      )}

      {/* Phase 2: result label */}
      {phase2FadeIn > 0 && (
        <div
          style={{
            position: "absolute",
            left: 0,
            top: LABEL_Y,
            width: 1920,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 20,
            fontWeight: 700,
            color: REMAINING_GREEN,
            opacity: phase2FadeIn,
            transform: `scale(${phase2Scale})`,
          }}
        >
          Same system. 5-10× more fits.
        </div>
      )}
    </>
  );
};

export default PhaseLabels;
