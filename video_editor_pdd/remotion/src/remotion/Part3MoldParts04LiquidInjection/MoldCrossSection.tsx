import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MOLD_LEFT,
  MOLD_TOP,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_STROKE,
  MOLD_STROKE_WIDTH,
  NOZZLE_X,
  NOZZLE_Y,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  NOZZLE_COLOR,
  NOZZLE_OPACITY,
  WALL_GLOW_COLOR,
  WALL_BASE_OPACITY,
  WALL_PEAK_OPACITY,
  WALLS,
  FONT_MONO,
  FRAME_WALL_GLOW_START,
  FRAME_WALL_GLOW_END,
} from './constants';

export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // Wall glow ramps from base to peak over frames 510-570
  const wallGlow = interpolate(
    frame,
    [FRAME_WALL_GLOW_START, FRAME_WALL_GLOW_END],
    [WALL_BASE_OPACITY, WALL_PEAK_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute' }}
        viewBox="0 0 1920 1080"
      >
        {/* Outer mold shell */}
        <rect
          x={MOLD_LEFT}
          y={MOLD_TOP}
          width={MOLD_WIDTH}
          height={MOLD_HEIGHT}
          fill="none"
          stroke={MOLD_STROKE}
          strokeWidth={MOLD_STROKE_WIDTH}
          rx={12}
        />

        {/* Inner cavity outline */}
        <rect
          x={MOLD_LEFT + 40}
          y={MOLD_TOP + 40}
          width={MOLD_WIDTH - 80}
          height={MOLD_HEIGHT - 80}
          fill="none"
          stroke={MOLD_STROKE}
          strokeWidth={1.5}
          strokeDasharray="8 4"
          opacity={0.4}
          rx={8}
        />

        {/* Nozzle */}
        <g opacity={NOZZLE_OPACITY}>
          <path
            d={`M ${NOZZLE_X - NOZZLE_WIDTH / 2} ${NOZZLE_Y}
                L ${NOZZLE_X - 12} ${NOZZLE_Y + NOZZLE_HEIGHT}
                L ${NOZZLE_X + 12} ${NOZZLE_Y + NOZZLE_HEIGHT}
                L ${NOZZLE_X + NOZZLE_WIDTH / 2} ${NOZZLE_Y}
                Z`}
            fill={NOZZLE_COLOR}
            stroke={NOZZLE_COLOR}
            strokeWidth={1.5}
          />
          {/* Nozzle opening */}
          <circle
            cx={NOZZLE_X}
            cy={NOZZLE_Y + NOZZLE_HEIGHT}
            r={6}
            fill={NOZZLE_COLOR}
          />
        </g>

        {/* Walls */}
        {WALLS.map((wall) => (
          <g key={wall.id}>
            {/* Wall glow (background) */}
            <rect
              x={wall.x - 4}
              y={wall.y - 4}
              width={wall.width + 8}
              height={wall.height + 8}
              fill={WALL_GLOW_COLOR}
              opacity={wallGlow * 0.5}
              rx={4}
              filter="url(#wallBlur)"
            />
            {/* Wall solid */}
            <rect
              x={wall.x}
              y={wall.y}
              width={wall.width}
              height={wall.height}
              fill={WALL_GLOW_COLOR}
              opacity={wallGlow}
              rx={2}
            />
            {/* Wall label */}
            <text
              x={wall.width > wall.height ? wall.x + wall.width / 2 : wall.x + 16}
              y={wall.width > wall.height ? wall.y - 12 : wall.y + wall.height / 2}
              fill={WALL_GLOW_COLOR}
              opacity={Math.min(wallGlow + 0.2, 1)}
              fontSize={14}
              fontFamily={FONT_MONO}
              textAnchor="middle"
              dominantBaseline="central"
            >
              {wall.label}
            </text>
          </g>
        ))}

        {/* SVG filter for wall glow */}
        <defs>
          <filter id="wallBlur" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur in="SourceGraphic" stdDeviation="6" />
          </filter>
        </defs>
      </svg>
    </AbsoluteFill>
  );
};
