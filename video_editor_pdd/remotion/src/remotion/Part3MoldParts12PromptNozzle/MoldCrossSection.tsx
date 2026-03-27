import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  MOLD_TOP,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_WALL_THICKNESS,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  WALL_BLUE,
  AMBER,
  PHASE_NOZZLE_GLOW_END,
  PHASE_HOLD_START,
  DURATION_FRAMES,
} from "./constants";

interface MoldCrossSectionProps {
  wallsOpacity: number;
  nozzleGlowOpacity: number;
}

export const MoldCrossSection: React.FC<MoldCrossSectionProps> = ({
  wallsOpacity,
  nozzleGlowOpacity,
}) => {
  const frame = useCurrentFrame();

  // Nozzle glow animates in over first 30 frames
  const glowProgress = interpolate(frame, [0, PHASE_NOZZLE_GLOW_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Walls dim from 0.5 to wallsOpacity over first 30 frames
  const currentWallOpacity = interpolate(
    frame,
    [0, PHASE_NOZZLE_GLOW_END],
    [0.5, wallsOpacity],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Walls glow at end (600-720)
  const wallGlowOpacity = interpolate(
    frame,
    [PHASE_HOLD_START, PHASE_HOLD_START + 60, DURATION_FRAMES],
    [currentWallOpacity, 0.6, 0.6],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const moldLeft = MOLD_CENTER_X - MOLD_WIDTH / 2;
  const moldRight = MOLD_CENTER_X + MOLD_WIDTH / 2;
  const nozzleLeft = MOLD_CENTER_X - NOZZLE_WIDTH / 2;
  const nozzleRight = MOLD_CENTER_X + NOZZLE_WIDTH / 2;
  const nozzleTopY = MOLD_TOP - NOZZLE_HEIGHT;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        <filter id="nozzleGlow">
          <feGaussianBlur stdDeviation="15" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
        <filter id="wallGlow">
          <feGaussianBlur stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Mold walls — U-shape */}
      <g opacity={wallGlowOpacity} filter={frame >= PHASE_HOLD_START ? "url(#wallGlow)" : undefined}>
        {/* Left wall */}
        <rect
          x={moldLeft}
          y={MOLD_TOP}
          width={MOLD_WALL_THICKNESS}
          height={MOLD_HEIGHT}
          fill={WALL_BLUE}
        />
        {/* Right wall */}
        <rect
          x={moldRight - MOLD_WALL_THICKNESS}
          y={MOLD_TOP}
          width={MOLD_WALL_THICKNESS}
          height={MOLD_HEIGHT}
          fill={WALL_BLUE}
        />
        {/* Bottom wall */}
        <rect
          x={moldLeft}
          y={MOLD_TOP + MOLD_HEIGHT - MOLD_WALL_THICKNESS}
          width={MOLD_WIDTH}
          height={MOLD_WALL_THICKNESS}
          fill={WALL_BLUE}
        />
        {/* Top-left wall (left of nozzle) */}
        <rect
          x={moldLeft}
          y={MOLD_TOP}
          width={nozzleLeft - moldLeft}
          height={MOLD_WALL_THICKNESS}
          fill={WALL_BLUE}
        />
        {/* Top-right wall (right of nozzle) */}
        <rect
          x={nozzleRight}
          y={MOLD_TOP}
          width={moldRight - nozzleRight}
          height={MOLD_WALL_THICKNESS}
          fill={WALL_BLUE}
        />
      </g>

      {/* Nozzle — funnel shape */}
      <g
        opacity={glowProgress * nozzleGlowOpacity}
        filter="url(#nozzleGlow)"
      >
        {/* Nozzle body — trapezoid using polygon */}
        <polygon
          points={`
            ${MOLD_CENTER_X - NOZZLE_WIDTH * 1.2},${nozzleTopY}
            ${MOLD_CENTER_X + NOZZLE_WIDTH * 1.2},${nozzleTopY}
            ${nozzleRight},${MOLD_TOP}
            ${nozzleLeft},${MOLD_TOP}
          `}
          fill={AMBER}
          opacity={0.7}
        />
        {/* Nozzle opening — small rect at bottom */}
        <rect
          x={nozzleLeft}
          y={MOLD_TOP - 4}
          width={NOZZLE_WIDTH}
          height={8}
          fill={AMBER}
          opacity={0.9}
        />
      </g>
    </svg>
  );
};
