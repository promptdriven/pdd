import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { TEXT_PRIMARY, AMBER, TIMING } from "./constants";

/**
 * "When these conflict, tests win. Always."
 * Appears at frame 310, with amber emphasis on key phrases and an animated underline.
 */
export const ConflictLine: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [TIMING.conflictStart, TIMING.conflictStart + 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Underline draw animation (15 frames after text appears)
  const underlineProgress = interpolate(
    frame,
    [TIMING.conflictStart + 10, TIMING.conflictStart + 25],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
  );

  // Pulsing glow on key phrases
  const glowPulse =
    frame >= TIMING.conflictStart
      ? interpolate(
          (frame - TIMING.conflictStart) % 30,
          [0, 15, 30],
          [0.8, 1, 0.8],
          { extrapolateRight: "clamp" }
        )
      : 0.8;

  return (
    <div
      style={{
        position: "absolute",
        left: 650,
        right: 100,
        top: 700,
        textAlign: "center",
        opacity: fadeIn,
      }}
    >
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 18,
          color: TEXT_PRIMARY,
          opacity: 0.8,
          display: "inline",
        }}
      >
        <span>When these conflict, </span>
        <span
          style={{
            fontWeight: 700,
            color: AMBER,
            opacity: glowPulse,
            textShadow: `0 0 12px ${AMBER}40`,
          }}
        >
          tests win
        </span>
        <span>. </span>
        <span
          style={{
            fontWeight: 700,
            color: AMBER,
            opacity: glowPulse,
            textShadow: `0 0 12px ${AMBER}40`,
          }}
        >
          Always.
        </span>
      </div>

      {/* Animated underline under "tests win. Always." */}
      <div
        style={{
          position: "relative",
          margin: "0 auto",
          marginTop: 6,
          width: 240,
          height: 2,
          overflow: "hidden",
        }}
      >
        <div
          style={{
            position: "absolute",
            left: 0,
            top: 0,
            height: 2,
            width: `${underlineProgress * 100}%`,
            backgroundColor: AMBER,
            opacity: 0.3,
            borderRadius: 1,
          }}
        />
      </div>
    </div>
  );
};
