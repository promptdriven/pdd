import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_COLOR,
  PART_COLOR,
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_HALF_WIDTH,
  MOLD_HALF_HEIGHT,
  MOLD_GAP_OPEN,
  PART_WIDTH,
  PART_HEIGHT,
  MOLD_START_SPEED,
  MOLD_END_SPEED,
  TOTAL_FRAMES,
} from "./constants";

/**
 * Returns the current cycle speed (frames per cycle) at a given frame,
 * easing from MOLD_START_SPEED down to MOLD_END_SPEED using easeIn(quad).
 */
function getCycleSpeed(frame: number): number {
  const t = interpolate(frame, [0, TOTAL_FRAMES], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.quad),
  });
  return MOLD_START_SPEED - t * (MOLD_START_SPEED - MOLD_END_SPEED);
}

/**
 * Returns the phase within the current cycle [0..1].
 * 0 = mold fully closed, 0.5 = mold fully open (part ejects), 1 = mold closed again.
 * We accumulate fractional cycle progress frame-by-frame.
 */
function getCyclePhase(frame: number): number {
  let accumulated = 0;
  for (let f = 0; f < frame; f++) {
    const speed = getCycleSpeed(f);
    accumulated += 1 / speed;
  }
  return accumulated % 1;
}

/**
 * A simple 2D mold cross-section animation.
 * Two mold halves open/close horizontally, a plastic part ejects upward when open.
 */
export const MoldCycleAnimation: React.FC = () => {
  const frame = useCurrentFrame();

  const phase = getCyclePhase(frame);

  // Mold opening: phase 0→0.3 open, 0.3→0.5 hold, 0.5→0.8 close, 0.8→1 hold closed
  const openAmount = (() => {
    if (phase < 0.3) {
      // opening
      return interpolate(phase, [0, 0.3], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      });
    }
    if (phase < 0.5) {
      return 1; // fully open
    }
    if (phase < 0.8) {
      // closing
      return interpolate(phase, [0.5, 0.8], [1, 0], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.in(Easing.quad),
      });
    }
    return 0; // fully closed
  })();

  const gapX = openAmount * MOLD_GAP_OPEN;

  // Part ejection: eject upward during open phase (0.3→0.5)
  const partProgress = (() => {
    if (phase >= 0.25 && phase < 0.55) {
      return interpolate(phase, [0.25, 0.55], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      });
    }
    return phase >= 0.55 ? 1 : 0;
  })();

  const partEjectY = partProgress * 200; // pixels upward
  const partOpacity = (() => {
    if (phase < 0.25) return 0;
    if (phase < 0.55) return 1;
    // fade out after ejection
    return interpolate(phase, [0.55, 0.7], [1, 0], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });
  })();

  // Subtle glow around the mold area
  const glowOpacity = interpolate(frame, [0, 60, 180, 300], [0.3, 0.5, 0.7, 0.8], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
      }}
    >
      {/* Ambient glow behind mold */}
      <div
        style={{
          position: "absolute",
          left: MOLD_CENTER_X - 200,
          top: MOLD_CENTER_Y - 200,
          width: 400,
          height: 400,
          borderRadius: "50%",
          background: `radial-gradient(circle, rgba(217,148,74,${glowOpacity * 0.15}) 0%, transparent 70%)`,
        }}
      />

      {/* Left mold half */}
      <div
        style={{
          position: "absolute",
          left: MOLD_CENTER_X - MOLD_HALF_WIDTH - gapX / 2,
          top: MOLD_CENTER_Y - MOLD_HALF_HEIGHT / 2,
          width: MOLD_HALF_WIDTH,
          height: MOLD_HALF_HEIGHT,
          backgroundColor: MOLD_COLOR,
          borderRadius: "8px 0 0 8px",
          boxShadow: "inset -4px 0 12px rgba(0,0,0,0.4), 2px 4px 16px rgba(0,0,0,0.3)",
        }}
      >
        {/* Cavity cutout on right side */}
        <div
          style={{
            position: "absolute",
            right: 0,
            top: MOLD_HALF_HEIGHT / 2 - PART_HEIGHT / 2,
            width: PART_WIDTH / 2 + 4,
            height: PART_HEIGHT + 8,
            backgroundColor: "#4A5568",
            borderRadius: "4px 0 0 4px",
          }}
        />
      </div>

      {/* Right mold half */}
      <div
        style={{
          position: "absolute",
          left: MOLD_CENTER_X + gapX / 2,
          top: MOLD_CENTER_Y - MOLD_HALF_HEIGHT / 2,
          width: MOLD_HALF_WIDTH,
          height: MOLD_HALF_HEIGHT,
          backgroundColor: MOLD_COLOR,
          borderRadius: "0 8px 8px 0",
          boxShadow: "inset 4px 0 12px rgba(0,0,0,0.4), -2px 4px 16px rgba(0,0,0,0.3)",
        }}
      >
        {/* Cavity cutout on left side */}
        <div
          style={{
            position: "absolute",
            left: 0,
            top: MOLD_HALF_HEIGHT / 2 - PART_HEIGHT / 2,
            width: PART_WIDTH / 2 + 4,
            height: PART_HEIGHT + 8,
            backgroundColor: "#4A5568",
            borderRadius: "0 4px 4px 0",
          }}
        />
      </div>

      {/* Ejected plastic part */}
      {partOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: MOLD_CENTER_X - PART_WIDTH / 2,
            top: MOLD_CENTER_Y - PART_HEIGHT / 2 - partEjectY,
            width: PART_WIDTH,
            height: PART_HEIGHT,
            backgroundColor: PART_COLOR,
            borderRadius: 6,
            opacity: partOpacity,
            boxShadow: `0 4px 20px rgba(217, 148, 74, ${partOpacity * 0.5})`,
          }}
        />
      )}

      {/* Static part in mold cavity (when mold is closed) */}
      {openAmount < 0.15 && (
        <div
          style={{
            position: "absolute",
            left: MOLD_CENTER_X - PART_WIDTH / 2,
            top: MOLD_CENTER_Y - PART_HEIGHT / 2,
            width: PART_WIDTH,
            height: PART_HEIGHT,
            backgroundColor: PART_COLOR,
            borderRadius: 6,
            opacity: 0.6,
          }}
        />
      )}
    </div>
  );
};

export default MoldCycleAnimation;
