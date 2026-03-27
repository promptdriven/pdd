import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_W,
  CANVAS_H,
  GHOST_WALLS_COLOR,
  GHOST_WALLS_OPACITY,
  GHOST_NOZZLE_COLOR,
  GHOST_NOZZLE_OPACITY,
  GHOST_CAVITY_COLOR,
  GHOST_CAVITY_OPACITY,
  GHOST_STROKE_WIDTH,
  GHOST_DRAW_START,
  GHOST_DRAW_DURATION,
  PULSE_CYCLE_FRAMES,
  FADEOUT_START,
  FADEOUT_DURATION,
} from "./constants";

/**
 * Ghost mold cross-section: three outlined regions (walls, nozzle, cavity)
 * drawn via stroke-dashoffset animation, with subtle pulsing during hold.
 */
export const GhostMold: React.FC = () => {
  const frame = useCurrentFrame();

  // Stroke draw-in progress (0→1 over GHOST_DRAW_DURATION starting at GHOST_DRAW_START)
  const drawProgress = interpolate(
    frame,
    [GHOST_DRAW_START, GHOST_DRAW_START + GHOST_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Fade-out at end
  const fadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  // Pulsing: walls pulse on phase 0, nozzle on phase 1, cavity on phase 2
  const pulseForRegion = (phaseOffset: number): number => {
    if (frame < GHOST_DRAW_START + GHOST_DRAW_DURATION) return 1;
    const cycleFrame = (frame - (GHOST_DRAW_START + GHOST_DRAW_DURATION) + phaseOffset * 20) % PULSE_CYCLE_FRAMES;
    return interpolate(
      cycleFrame,
      [0, PULSE_CYCLE_FRAMES / 2, PULSE_CYCLE_FRAMES],
      [1, 1.8, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.sin) }
    );
  };

  const wallsPulse = pulseForRegion(0);
  const nozzlePulse = pulseForRegion(1);
  const cavityPulse = pulseForRegion(2);

  // Mold outline path lengths (approximate)
  const wallsPathLength = 900;
  const nozzlePathLength = 300;
  const cavityPathLength = 500;

  const cx = CANVAS_W / 2;
  const cy = CANVAS_H / 2;

  return (
    <AbsoluteFill style={{ opacity: fadeOut }}>
      <svg
        width={CANVAS_W}
        height={CANVAS_H}
        viewBox={`0 0 ${CANVAS_W} ${CANVAS_H}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Walls region — outer mold shell */}
        <path
          d={`
            M ${cx - 200} ${cy - 140}
            L ${cx + 200} ${cy - 140}
            L ${cx + 200} ${cy + 140}
            L ${cx - 200} ${cy + 140}
            Z
            M ${cx - 160} ${cy - 100}
            L ${cx + 160} ${cy - 100}
            L ${cx + 160} ${cy + 100}
            L ${cx - 160} ${cy + 100}
            Z
          `}
          fill="none"
          stroke={GHOST_WALLS_COLOR}
          strokeWidth={GHOST_STROKE_WIDTH}
          strokeOpacity={GHOST_WALLS_OPACITY * wallsPulse}
          strokeDasharray={wallsPathLength}
          strokeDashoffset={wallsPathLength * (1 - drawProgress)}
          fillRule="evenodd"
        />

        {/* Nozzle region — top funnel */}
        <path
          d={`
            M ${cx - 30} ${cy - 140}
            L ${cx - 15} ${cy - 180}
            L ${cx + 15} ${cy - 180}
            L ${cx + 30} ${cy - 140}
            M ${cx - 8} ${cy - 180}
            L ${cx - 8} ${cy - 210}
            L ${cx + 8} ${cy - 210}
            L ${cx + 8} ${cy - 180}
          `}
          fill="none"
          stroke={GHOST_NOZZLE_COLOR}
          strokeWidth={GHOST_STROKE_WIDTH}
          strokeOpacity={GHOST_NOZZLE_OPACITY * nozzlePulse}
          strokeDasharray={nozzlePathLength}
          strokeDashoffset={nozzlePathLength * (1 - drawProgress)}
        />

        {/* Cavity region — inner shape */}
        <path
          d={`
            M ${cx - 100} ${cy - 50}
            C ${cx - 100} ${cy - 80}, ${cx - 60} ${cy - 90}, ${cx} ${cy - 90}
            C ${cx + 60} ${cy - 90}, ${cx + 100} ${cy - 80}, ${cx + 100} ${cy - 50}
            L ${cx + 100} ${cy + 50}
            C ${cx + 100} ${cy + 80}, ${cx + 60} ${cy + 90}, ${cx} ${cy + 90}
            C ${cx - 60} ${cy + 90}, ${cx - 100} ${cy + 80}, ${cx - 100} ${cy + 50}
            Z
          `}
          fill="none"
          stroke={GHOST_CAVITY_COLOR}
          strokeWidth={GHOST_STROKE_WIDTH}
          strokeOpacity={GHOST_CAVITY_OPACITY * cavityPulse}
          strokeDasharray={cavityPathLength}
          strokeDashoffset={cavityPathLength * (1 - drawProgress)}
        />

        {/* Small channel lines connecting nozzle to cavity */}
        <line
          x1={cx}
          y1={cy - 140}
          x2={cx}
          y2={cy - 90}
          stroke={GHOST_NOZZLE_COLOR}
          strokeWidth={GHOST_STROKE_WIDTH}
          strokeOpacity={GHOST_NOZZLE_OPACITY * nozzlePulse * 0.7}
          strokeDasharray={50}
          strokeDashoffset={50 * (1 - drawProgress)}
        />
      </svg>
    </AbsoluteFill>
  );
};

export default GhostMold;
