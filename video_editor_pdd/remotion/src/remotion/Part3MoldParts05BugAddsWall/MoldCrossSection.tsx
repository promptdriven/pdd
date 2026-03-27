import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MOLD_X,
  MOLD_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_WALL_THICKNESS,
  NOZZLE_X,
  NOZZLE_Y,
  EXISTING_WALLS,
  WALL_EXISTING_COLOR,
  TEXT_PRIMARY,
} from './constants';

interface MoldCrossSectionProps {
  wallsOpacity: number;
}

export const MoldCrossSection: React.FC<MoldCrossSectionProps> = ({
  wallsOpacity,
}) => {
  const frame = useCurrentFrame();

  // Subtle wall shimmer
  const shimmer = interpolate(
    frame % 120,
    [0, 60, 120],
    [0.35, 0.45, 0.35],
    { extrapolateRight: 'clamp' }
  );

  const outerOpacity = Math.max(wallsOpacity, shimmer);

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="wallGlow" x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur stdDeviation="4" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Outer mold walls */}
      {/* Top wall */}
      <rect
        x={MOLD_X}
        y={MOLD_Y}
        width={MOLD_WIDTH}
        height={MOLD_WALL_THICKNESS}
        fill={WALL_EXISTING_COLOR}
        opacity={outerOpacity}
        filter="url(#wallGlow)"
      />
      {/* Bottom wall */}
      <rect
        x={MOLD_X}
        y={MOLD_Y + MOLD_HEIGHT - MOLD_WALL_THICKNESS}
        width={MOLD_WIDTH}
        height={MOLD_WALL_THICKNESS}
        fill={WALL_EXISTING_COLOR}
        opacity={outerOpacity}
        filter="url(#wallGlow)"
      />
      {/* Left wall */}
      <rect
        x={MOLD_X}
        y={MOLD_Y}
        width={MOLD_WALL_THICKNESS}
        height={MOLD_HEIGHT}
        fill={WALL_EXISTING_COLOR}
        opacity={outerOpacity}
        filter="url(#wallGlow)"
      />
      {/* Right wall */}
      <rect
        x={MOLD_X + MOLD_WIDTH - MOLD_WALL_THICKNESS}
        y={MOLD_Y}
        width={MOLD_WALL_THICKNESS}
        height={MOLD_HEIGHT}
        fill={WALL_EXISTING_COLOR}
        opacity={outerOpacity}
        filter="url(#wallGlow)"
      />

      {/* Nozzle */}
      <polygon
        points={`${NOZZLE_X - 20},${NOZZLE_Y - 30} ${NOZZLE_X + 20},${NOZZLE_Y - 30} ${NOZZLE_X + 8},${NOZZLE_Y} ${NOZZLE_X - 8},${NOZZLE_Y}`}
        fill={WALL_EXISTING_COLOR}
        opacity={outerOpacity * 0.8}
      />

      {/* Internal walls */}
      {EXISTING_WALLS.map((wall, i) => (
        <g key={`wall-${i}`}>
          <rect
            x={wall.x}
            y={wall.y}
            width={wall.width}
            height={wall.height}
            fill={WALL_EXISTING_COLOR}
            opacity={outerOpacity}
            filter="url(#wallGlow)"
          />
          {/* Wall label */}
          <text
            x={wall.x + wall.width / 2}
            y={wall.y - 10}
            textAnchor="middle"
            fontFamily="'JetBrains Mono', monospace"
            fontSize={11}
            fill={TEXT_PRIMARY}
            opacity={outerOpacity * 0.7}
          >
            {wall.label}
          </text>
        </g>
      ))}
    </svg>
  );
};
