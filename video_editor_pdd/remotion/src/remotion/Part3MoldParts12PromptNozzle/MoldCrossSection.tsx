import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WALL_COLOR,
  WALL_DIM_OPACITY,
  WALL_GLOW_OPACITY,
  NOZZLE_COLOR,
  NOZZLE_GLOW_BLUR,
  NOZZLE_GLOW_OPACITY,
  MOLD_LEFT,
  MOLD_TOP,
  MOLD_OUTER_W,
  MOLD_OUTER_H,
  MOLD_WALL_THICKNESS,
  MOLD_INNER_W,
  MOLD_INNER_H,
  MOLD_INNER_LEFT,
  MOLD_INNER_TOP,
  NOZZLE_X,
  NOZZLE_Y,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  MOLD_CENTER_X,
  PHASE_NOZZLE_GLOW_END,
  PHASE_HOLD_START,
  TOTAL_FRAMES,
} from "./constants";

export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // Nozzle glows in over first 30 frames
  const nozzleGlow = interpolate(frame, [0, PHASE_NOZZLE_GLOW_END], [0, 1], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Walls dim at start, glow at end (600-720)
  const wallOpacity = interpolate(
    frame,
    [0, PHASE_NOZZLE_GLOW_END, PHASE_HOLD_START, TOTAL_FRAMES],
    [0.3, WALL_DIM_OPACITY, WALL_DIM_OPACITY, WALL_GLOW_OPACITY],
    { extrapolateRight: "clamp" }
  );

  // Wall glow at end
  const wallGlowBlur = interpolate(
    frame,
    [PHASE_HOLD_START, TOTAL_FRAMES],
    [0, 8],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        <filter id="nozzleGlow">
          <feGaussianBlur
            stdDeviation={NOZZLE_GLOW_BLUR}
            result="blur"
          />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
        <filter id="wallGlow">
          <feGaussianBlur stdDeviation={wallGlowBlur} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Outer mold walls */}
      <rect
        x={MOLD_LEFT}
        y={MOLD_TOP}
        width={MOLD_OUTER_W}
        height={MOLD_OUTER_H}
        rx={6}
        fill="none"
        stroke={WALL_COLOR}
        strokeWidth={MOLD_WALL_THICKNESS}
        opacity={wallOpacity}
        filter={wallGlowBlur > 0 ? "url(#wallGlow)" : undefined}
      />

      {/* Inner cavity (dark) */}
      <rect
        x={MOLD_INNER_LEFT}
        y={MOLD_INNER_TOP}
        width={MOLD_INNER_W}
        height={MOLD_INNER_H}
        fill="#0A0F1A"
        opacity={0.8}
      />

      {/* Nozzle (trapezoid shape at top center) */}
      <g opacity={nozzleGlow} filter="url(#nozzleGlow)">
        {/* Nozzle body - trapezoid */}
        <polygon
          points={`
            ${NOZZLE_X},${NOZZLE_Y + NOZZLE_HEIGHT}
            ${NOZZLE_X + NOZZLE_WIDTH},${NOZZLE_Y + NOZZLE_HEIGHT}
            ${NOZZLE_X + NOZZLE_WIDTH - 15},${NOZZLE_Y}
            ${NOZZLE_X + 15},${NOZZLE_Y}
          `}
          fill={NOZZLE_COLOR}
          opacity={NOZZLE_GLOW_OPACITY}
          stroke={NOZZLE_COLOR}
          strokeWidth={2}
        />
        {/* Nozzle opening */}
        <rect
          x={MOLD_CENTER_X - 15}
          y={NOZZLE_Y + NOZZLE_HEIGHT - 5}
          width={30}
          height={15}
          fill={NOZZLE_COLOR}
          opacity={0.7}
        />
      </g>
    </svg>
  );
};
