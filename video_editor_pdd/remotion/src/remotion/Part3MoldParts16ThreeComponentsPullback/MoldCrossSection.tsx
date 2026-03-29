import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  MOLD_SHELL_COLOR,
  MOLD_SHELL_STROKE,
  NOZZLE_COLOR,
  NOZZLE_GLOW_OPACITY,
  WALL_COLOR,
  WALL_GLOW_OPACITY,
  CAVITY_COLOR,
  CAVITY_FILL_OPACITY,
  MOLD_CENTER_X,
  MOLD_WIDTH,
  MOLD_LEFT,
  MOLD_RIGHT,
  NOZZLE_TOP,
  NOZZLE_BOTTOM,
  NOZZLE_NECK_WIDTH,
  CAVITY_TOP,
  CAVITY_BOTTOM,
  WALL_THICKNESS,
  EXIT_TOP,
  EXIT_BOTTOM,
  EXIT_NECK_WIDTH,
  MOLD_FADE_IN_FRAMES,
  LABEL_MUTED_COLOR,
} from './constants';

export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, MOLD_FADE_IN_FRAMES], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const nozzleLeft = MOLD_CENTER_X - NOZZLE_NECK_WIDTH / 2;
  const nozzleRight = MOLD_CENTER_X + NOZZLE_NECK_WIDTH / 2;
  const exitLeft = MOLD_CENTER_X - EXIT_NECK_WIDTH / 2;
  const exitRight = MOLD_CENTER_X + EXIT_NECK_WIDTH / 2;

  // Outer mold shell path (full cross-section)
  const shellPath = `
    M ${nozzleLeft} ${NOZZLE_TOP}
    L ${nozzleLeft} ${NOZZLE_BOTTOM}
    L ${MOLD_LEFT} ${NOZZLE_BOTTOM}
    L ${MOLD_LEFT} ${EXIT_TOP}
    L ${exitLeft} ${EXIT_TOP}
    L ${exitLeft} ${EXIT_BOTTOM}
    M ${exitRight} ${EXIT_BOTTOM}
    L ${exitRight} ${EXIT_TOP}
    L ${MOLD_RIGHT} ${EXIT_TOP}
    L ${MOLD_RIGHT} ${NOZZLE_BOTTOM}
    L ${nozzleRight} ${NOZZLE_BOTTOM}
    L ${nozzleRight} ${NOZZLE_TOP}
  `;

  return (
    <AbsoluteFill style={{ opacity }}>
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          {/* Nozzle glow filter */}
          <filter id="nozzleGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="8" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
          {/* Wall glow filter */}
          <filter id="wallGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="6" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Cavity fill */}
        <rect
          x={MOLD_LEFT + WALL_THICKNESS}
          y={CAVITY_TOP}
          width={MOLD_WIDTH - WALL_THICKNESS * 2}
          height={CAVITY_BOTTOM - CAVITY_TOP}
          fill={CAVITY_COLOR}
          opacity={CAVITY_FILL_OPACITY}
        />

        {/* Nozzle region glow */}
        <rect
          x={nozzleLeft}
          y={NOZZLE_TOP}
          width={NOZZLE_NECK_WIDTH}
          height={NOZZLE_BOTTOM - NOZZLE_TOP}
          fill={NOZZLE_COLOR}
          opacity={NOZZLE_GLOW_OPACITY}
          filter="url(#nozzleGlow)"
          rx={4}
        />

        {/* Wall regions (left and right) */}
        <rect
          x={MOLD_LEFT}
          y={CAVITY_TOP}
          width={WALL_THICKNESS}
          height={CAVITY_BOTTOM - CAVITY_TOP}
          fill={WALL_COLOR}
          opacity={WALL_GLOW_OPACITY}
          filter="url(#wallGlow)"
        />
        <rect
          x={MOLD_RIGHT - WALL_THICKNESS}
          y={CAVITY_TOP}
          width={WALL_THICKNESS}
          height={CAVITY_BOTTOM - CAVITY_TOP}
          fill={WALL_COLOR}
          opacity={WALL_GLOW_OPACITY}
          filter="url(#wallGlow)"
        />

        {/* Outer shell */}
        <path
          d={shellPath}
          fill="none"
          stroke={MOLD_SHELL_COLOR}
          strokeWidth={MOLD_SHELL_STROKE}
          strokeLinejoin="round"
        />

        {/* Component labels on the left side */}
        <text
          x={MOLD_LEFT - 30}
          y={(NOZZLE_TOP + NOZZLE_BOTTOM) / 2}
          fill={LABEL_MUTED_COLOR}
          fontSize={12}
          fontFamily="Inter, sans-serif"
          textAnchor="end"
          dominantBaseline="middle"
        >
          Nozzle
        </text>
        <text
          x={MOLD_LEFT - 30}
          y={(CAVITY_TOP + CAVITY_BOTTOM) / 2}
          fill={LABEL_MUTED_COLOR}
          fontSize={12}
          fontFamily="Inter, sans-serif"
          textAnchor="end"
          dominantBaseline="middle"
        >
          Cavity
        </text>
        <text
          x={MOLD_LEFT - 30}
          y={(EXIT_TOP + EXIT_BOTTOM) / 2}
          fill={LABEL_MUTED_COLOR}
          fontSize={12}
          fontFamily="Inter, sans-serif"
          textAnchor="end"
          dominantBaseline="middle"
        >
          Exit
        </text>
      </svg>
    </AbsoluteFill>
  );
};
