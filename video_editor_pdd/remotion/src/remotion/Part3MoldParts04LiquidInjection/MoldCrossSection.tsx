import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MOLD_STROKE_COLOR,
  MOLD_STROKE_WIDTH,
  NOZZLE_COLOR,
  NOZZLE_OPACITY,
  WALL_GLOW_COLOR,
  WALL_GLOW_INITIAL,
  WALL_GLOW_PEAK,
  WALL_LABEL_FONT,
  WALL_LABEL_SIZE,
  WALLS,
  MOLD_LEFT,
  MOLD_TOP,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  NOZZLE_X,
  NOZZLE_Y,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  CAVITY_TOP,
  CAVITY_BOTTOM,
  CAVITY_LEFT,
  CAVITY_RIGHT,
  PHASE_GLOW_INCREASE_START,
  PHASE_GLOW_INCREASE_DURATION,
} from './constants';

export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // Wall glow increases from frame 510 over 60 frames
  const wallGlow = interpolate(
    frame,
    [PHASE_GLOW_INCREASE_START, PHASE_GLOW_INCREASE_START + PHASE_GLOW_INCREASE_DURATION],
    [WALL_GLOW_INITIAL, WALL_GLOW_PEAK],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
      viewBox="0 0 1920 1080"
    >
      <defs>
        <filter id="wall-glow">
          <feGaussianBlur stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Outer mold shell */}
      <rect
        x={MOLD_LEFT}
        y={MOLD_TOP}
        width={MOLD_WIDTH}
        height={MOLD_HEIGHT}
        fill="none"
        stroke={MOLD_STROKE_COLOR}
        strokeWidth={MOLD_STROKE_WIDTH}
        rx={8}
      />

      {/* Inner cavity outline */}
      <rect
        x={CAVITY_LEFT}
        y={CAVITY_TOP}
        width={CAVITY_RIGHT - CAVITY_LEFT}
        height={CAVITY_BOTTOM - CAVITY_TOP}
        fill="none"
        stroke={MOLD_STROKE_COLOR}
        strokeWidth={1.5}
        strokeDasharray="8 4"
        opacity={0.4}
      />

      {/* Nozzle (entry point at top) */}
      <g opacity={NOZZLE_OPACITY}>
        <rect
          x={NOZZLE_X}
          y={NOZZLE_Y - NOZZLE_HEIGHT}
          width={NOZZLE_WIDTH}
          height={NOZZLE_HEIGHT}
          fill={NOZZLE_COLOR}
          rx={4}
        />
        {/* Nozzle tip triangle */}
        <polygon
          points={`${NOZZLE_X + 10},${NOZZLE_Y} ${NOZZLE_X + NOZZLE_WIDTH - 10},${NOZZLE_Y} ${NOZZLE_X + NOZZLE_WIDTH / 2},${NOZZLE_Y + 15}`}
          fill={NOZZLE_COLOR}
        />
      </g>

      {/* Walls */}
      {WALLS.map((wall) => (
        <g key={wall.id} filter="url(#wall-glow)">
          {/* Wall body */}
          <rect
            x={wall.x - 4}
            y={wall.y}
            width={8}
            height={wall.height}
            fill={WALL_GLOW_COLOR}
            opacity={wallGlow}
            rx={2}
          />
          {/* Wall label */}
          <text
            x={wall.x}
            y={wall.y - 12}
            textAnchor="middle"
            fill={WALL_GLOW_COLOR}
            fontFamily={WALL_LABEL_FONT}
            fontSize={WALL_LABEL_SIZE}
            opacity={wallGlow + 0.2}
          >
            {wall.label}
          </text>
        </g>
      ))}

      {/* Mold cross-hatching (material fill) */}
      {/* Top section */}
      <rect
        x={MOLD_LEFT + MOLD_STROKE_WIDTH}
        y={MOLD_TOP + MOLD_STROKE_WIDTH}
        width={MOLD_WIDTH - MOLD_STROKE_WIDTH * 2}
        height={CAVITY_TOP - MOLD_TOP - MOLD_STROKE_WIDTH}
        fill={MOLD_STROKE_COLOR}
        opacity={0.15}
      />
      {/* Bottom section */}
      <rect
        x={MOLD_LEFT + MOLD_STROKE_WIDTH}
        y={CAVITY_BOTTOM}
        width={MOLD_WIDTH - MOLD_STROKE_WIDTH * 2}
        height={MOLD_TOP + MOLD_HEIGHT - CAVITY_BOTTOM - MOLD_STROKE_WIDTH}
        fill={MOLD_STROKE_COLOR}
        opacity={0.15}
      />
      {/* Left section */}
      <rect
        x={MOLD_LEFT + MOLD_STROKE_WIDTH}
        y={CAVITY_TOP}
        width={CAVITY_LEFT - MOLD_LEFT - MOLD_STROKE_WIDTH}
        height={CAVITY_BOTTOM - CAVITY_TOP}
        fill={MOLD_STROKE_COLOR}
        opacity={0.15}
      />
      {/* Right section */}
      <rect
        x={CAVITY_RIGHT}
        y={CAVITY_TOP}
        width={MOLD_LEFT + MOLD_WIDTH - CAVITY_RIGHT - MOLD_STROKE_WIDTH}
        height={CAVITY_BOTTOM - CAVITY_TOP}
        fill={MOLD_STROKE_COLOR}
        opacity={0.15}
      />
    </svg>
  );
};
