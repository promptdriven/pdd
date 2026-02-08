import React from "react";
import { interpolate, useCurrentFrame } from "remotion";
import { BEATS, COLORS, YEAR_COUNTER } from "./constants";

export const YearCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Calculate current year based on time progress
  const currentYear = Math.round(
    interpolate(
      frame,
      [BEATS.TIME_PROGRESS_START, BEATS.TIME_PROGRESS_END],
      [YEAR_COUNTER.startYear, YEAR_COUNTER.endYear],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    )
  );

  // Fade in animation
  const opacity = interpolate(
    frame,
    [0, 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Subtle pulse when year changes (every ~6.75 frames = 40 years / 270 frames)
  const pulse = Math.sin(frame * 0.15) * 0.1 + 1;

  return (
    <div
      style={{
        position: "absolute",
        top: 40,
        right: 60,
        opacity,
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 48,
        fontWeight: 700,
        color: COLORS.TITLE,
        textShadow: `0 0 30px ${COLORS.LINE_BUY}, 0 4px 20px rgba(0,0,0,0.6)`,
        transform: `scale(${pulse})`,
        transformOrigin: "right center",
      }}
    >
      {currentYear}
    </div>
  );
};
