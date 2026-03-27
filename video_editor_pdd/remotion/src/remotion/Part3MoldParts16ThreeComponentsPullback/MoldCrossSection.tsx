// MoldCrossSection.tsx — fully annotated mold with nozzle, cavity, walls, exit
import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  MOLD_TOP,
  MOLD_LEFT,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  NOZZLE_TOP,
  EXIT_WIDTH,
  EXIT_HEIGHT,
  EXIT_TOP,
  COLOR_PROMPT,
  COLOR_GROUNDING,
  COLOR_WALLS,
  COLOR_SHELL,
  NOZZLE_GLOW_OPACITY,
  WALL_GLOW_OPACITY,
  CAVITY_FILL_OPACITY,
  MOLD_FADE_FRAMES,
} from "./constants";

export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(frame, [0, MOLD_FADE_FRAMES], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const nozzleLeft = MOLD_CENTER_X - NOZZLE_WIDTH / 2;
  const exitLeft = MOLD_CENTER_X - EXIT_WIDTH / 2;

  return (
    <svg
      width={1920}
      height={1080}
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        opacity: fadeIn,
      }}
    >
      <defs>
        {/* Glow filters */}
        <filter id="nozzleGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="8" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
        <filter id="wallGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Cavity fill — teal at low opacity */}
      <rect
        x={MOLD_LEFT + 20}
        y={MOLD_TOP + 20}
        width={MOLD_WIDTH - 40}
        height={MOLD_HEIGHT - 40}
        rx={8}
        fill={COLOR_GROUNDING}
        opacity={CAVITY_FILL_OPACITY}
      />

      {/* Outer shell */}
      <rect
        x={MOLD_LEFT}
        y={MOLD_TOP}
        width={MOLD_WIDTH}
        height={MOLD_HEIGHT}
        rx={12}
        fill="none"
        stroke={COLOR_SHELL}
        strokeWidth={3}
      />

      {/* Nozzle (top entry) — amber glow */}
      <g filter="url(#nozzleGlow)">
        {/* Nozzle funnel shape */}
        <path
          d={`
            M ${nozzleLeft - 20} ${NOZZLE_TOP}
            L ${nozzleLeft + NOZZLE_WIDTH + 20} ${NOZZLE_TOP}
            L ${nozzleLeft + NOZZLE_WIDTH} ${NOZZLE_TOP + NOZZLE_HEIGHT}
            L ${nozzleLeft} ${NOZZLE_TOP + NOZZLE_HEIGHT}
            Z
          `}
          fill="none"
          stroke={COLOR_PROMPT}
          strokeWidth={3}
          opacity={NOZZLE_GLOW_OPACITY}
        />
        {/* Nozzle opening */}
        <rect
          x={MOLD_CENTER_X - 25}
          y={MOLD_TOP - 5}
          width={50}
          height={25}
          rx={4}
          fill={COLOR_PROMPT}
          opacity={0.15}
          stroke={COLOR_PROMPT}
          strokeWidth={2}
        />
      </g>

      {/* Left wall — blue glow */}
      <g filter="url(#wallGlow)">
        <rect
          x={MOLD_LEFT}
          y={MOLD_TOP}
          width={20}
          height={MOLD_HEIGHT}
          rx={4}
          fill={COLOR_WALLS}
          opacity={WALL_GLOW_OPACITY * 0.5}
        />
      </g>

      {/* Right wall — blue glow */}
      <g filter="url(#wallGlow)">
        <rect
          x={MOLD_LEFT + MOLD_WIDTH - 20}
          y={MOLD_TOP}
          width={20}
          height={MOLD_HEIGHT}
          rx={4}
          fill={COLOR_WALLS}
          opacity={WALL_GLOW_OPACITY * 0.5}
        />
      </g>

      {/* Exit (bottom) */}
      <rect
        x={exitLeft}
        y={EXIT_TOP}
        width={EXIT_WIDTH}
        height={EXIT_HEIGHT}
        rx={6}
        fill="none"
        stroke={COLOR_SHELL}
        strokeWidth={2}
      />
      {/* Exit opening indicator */}
      <rect
        x={MOLD_CENTER_X - 20}
        y={MOLD_TOP + MOLD_HEIGHT - 5}
        width={40}
        height={15}
        rx={3}
        fill={COLOR_SHELL}
        opacity={0.3}
      />

      {/* Component labels — dim supporting text */}
      <text
        x={MOLD_LEFT - 30}
        y={NOZZLE_TOP + NOZZLE_HEIGHT / 2 + 5}
        fill="#64748B"
        fontSize={12}
        fontFamily="Inter, sans-serif"
        textAnchor="end"
      >
        Nozzle
      </text>
      <text
        x={MOLD_LEFT - 30}
        y={MOLD_TOP + MOLD_HEIGHT / 2 + 5}
        fill="#64748B"
        fontSize={12}
        fontFamily="Inter, sans-serif"
        textAnchor="end"
      >
        Cavity
      </text>
      <text
        x={MOLD_LEFT + MOLD_WIDTH + 30}
        y={MOLD_TOP + MOLD_HEIGHT / 2 + 5}
        fill="#64748B"
        fontSize={12}
        fontFamily="Inter, sans-serif"
        textAnchor="start"
      >
        Walls
      </text>
    </svg>
  );
};

export default MoldCrossSection;
