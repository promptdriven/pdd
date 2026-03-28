import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BADGE_X,
  BADGE_Y,
  BADGE_TEXT,
  BADGE_BG_OPACITY,
  BADGE_BORDER_WIDTH,
  BADGE_RADIUS,
  BADGE_LETTER_SPACING,
  GREEN_ACCENT,
  BADGE_START,
  BADGE_DURATION,
} from "./constants";

export const SourceOfTruthBadge: React.FC = () => {
  const frame = useCurrentFrame();

  const visible = frame >= BADGE_START;

  const scale = visible
    ? interpolate(
        frame,
        [BADGE_START, BADGE_START + BADGE_DURATION],
        [0.2, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.7)) }
      )
    : 0;

  const opacity = visible
    ? interpolate(
        frame,
        [BADGE_START, BADGE_START + 8],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  // Subtle glow pulse after fully visible
  const glowPulse = visible
    ? interpolate(
        frame,
        [BADGE_START + BADGE_DURATION, BADGE_START + BADGE_DURATION + 30],
        [0, 0.08],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  if (!visible) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: BADGE_X,
        top: BADGE_Y,
        transform: `translate(-50%, -50%) scale(${scale})`,
        opacity,
        padding: "8px 18px",
        borderRadius: BADGE_RADIUS,
        backgroundColor: `rgba(90, 170, 110, ${BADGE_BG_OPACITY})`,
        border: `${BADGE_BORDER_WIDTH}px solid ${GREEN_ACCENT}`,
        boxShadow: `0 0 16px rgba(90, 170, 110, ${0.2 + glowPulse})`,
        whiteSpace: "nowrap",
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 12,
          fontWeight: 700,
          color: GREEN_ACCENT,
          letterSpacing: BADGE_LETTER_SPACING,
        }}
      >
        {BADGE_TEXT}
      </span>
    </div>
  );
};
