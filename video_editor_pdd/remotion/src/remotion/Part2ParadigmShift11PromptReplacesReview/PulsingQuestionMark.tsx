import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  QUESTION_MARK_START,
  QUESTION_MARK_FADE_END,
  PULSE_PERIOD,
  QUESTION_MARK_SIZE,
  QUESTION_MARK_X,
  QUESTION_MARK_Y,
  QUESTION_MARK_BASE_OPACITY,
  QUESTION_MARK_PEAK_OPACITY,
  QUESTION_MARK_GLOW_BLUR,
  QUESTION_MARK_GLOW_OPACITY,
  RED_ACCENT,
} from "./constants";

export const PulsingQuestionMark: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < QUESTION_MARK_START) return null;

  // Fade in
  const fadeIn = interpolate(
    frame,
    [QUESTION_MARK_START, QUESTION_MARK_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulse using sine wave
  const cycleFrame = frame - QUESTION_MARK_START;
  const pulsePhase = (cycleFrame % PULSE_PERIOD) / PULSE_PERIOD;
  const sineValue = Math.sin(pulsePhase * Math.PI * 2);
  const pulseOpacity = interpolate(
    sineValue,
    [-1, 1],
    [QUESTION_MARK_BASE_OPACITY, QUESTION_MARK_PEAK_OPACITY]
  );

  const finalOpacity = fadeIn * pulseOpacity;

  return (
    <>
      {/* Glow layer */}
      <div
        style={{
          position: "absolute",
          left: QUESTION_MARK_X - QUESTION_MARK_SIZE / 2,
          top: QUESTION_MARK_Y - QUESTION_MARK_SIZE / 2,
          width: QUESTION_MARK_SIZE,
          height: QUESTION_MARK_SIZE,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          filter: `blur(${QUESTION_MARK_GLOW_BLUR}px)`,
          opacity: fadeIn * QUESTION_MARK_GLOW_OPACITY,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: QUESTION_MARK_SIZE,
            fontWeight: 700,
            color: RED_ACCENT,
            lineHeight: 1,
          }}
        >
          ?
        </span>
      </div>

      {/* Main question mark */}
      <div
        style={{
          position: "absolute",
          left: QUESTION_MARK_X - QUESTION_MARK_SIZE / 2,
          top: QUESTION_MARK_Y - QUESTION_MARK_SIZE / 2,
          width: QUESTION_MARK_SIZE,
          height: QUESTION_MARK_SIZE,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          opacity: finalOpacity,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: QUESTION_MARK_SIZE,
            fontWeight: 700,
            color: RED_ACCENT,
            lineHeight: 1,
          }}
        >
          ?
        </span>
      </div>
    </>
  );
};
