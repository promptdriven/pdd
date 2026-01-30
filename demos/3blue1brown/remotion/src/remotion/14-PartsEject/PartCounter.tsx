import React from "react";
import { useCurrentFrame } from "remotion";
import { COLORS, getPartsCount, formatCount, BEATS } from "./constants";

/**
 * Displays the "PARTS PRODUCED" label and animated counter number.
 * Glow intensity scales with rate of change.
 */
export const PartCounter: React.FC = () => {
  const frame = useCurrentFrame();

  const count = getPartsCount(frame);
  const displayCount = formatCount(count);

  // Glow intensity: pulses harder as count accelerates
  // Compare count at current frame vs 5 frames ago
  const prevCount = getPartsCount(Math.max(0, frame - 5));
  const delta = count - prevCount;
  const glowIntensity = Math.min(delta / 200, 1);
  const glowRadius = 8 + glowIntensity * 24;

  // Fade in the counter
  const counterOpacity = frame < 30 ? frame / 30 : 1;

  // During hold, keep a steady medium glow
  const holdGlow = frame >= BEATS.HOLD_START ? 16 : glowRadius;
  const finalGlowRadius = frame >= BEATS.HOLD_START ? holdGlow : glowRadius;

  return (
    <div
      style={{
        position: "absolute",
        top: 280,
        left: 1150,
        width: 400,
        textAlign: "center",
        opacity: counterOpacity,
      }}
    >
      {/* Label */}
      <div
        style={{
          fontSize: 18,
          fontFamily: "sans-serif",
          fontWeight: 600,
          textTransform: "uppercase" as const,
          letterSpacing: 2,
          color: COLORS.LABEL_GRAY,
          marginBottom: 16,
        }}
      >
        Parts Produced
      </div>

      {/* Counter number */}
      <div
        style={{
          fontSize: 72,
          fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
          fontWeight: 700,
          color: COLORS.COUNTER_WHITE,
          textShadow: `0 0 ${finalGlowRadius}px ${COLORS.COUNTER_GLOW}, 0 0 ${finalGlowRadius * 2}px ${COLORS.COUNTER_GLOW}`,
          lineHeight: 1,
        }}
      >
        {displayCount}
      </div>
    </div>
  );
};
