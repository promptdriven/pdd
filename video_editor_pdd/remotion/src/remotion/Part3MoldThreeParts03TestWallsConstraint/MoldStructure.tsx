import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  WALL_SEGMENTS,
  WALL_COLOR_DIM,
  WALL_STROKE,
  CAVITY_COLOR,
  LABEL_DIM,
  MOLD_LEFT,
  MOLD_RIGHT,
  MOLD_TOP,
  MOLD_BOTTOM,
  NOZZLE_X,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  MONO_FONT,
  WALL_COLOR,
  WallSegment,
} from './constants';

interface MoldStructureProps {
  focusWallId?: string;
  focusProgress: number; // 0..1
  wallFlashes: Record<string, number>; // wallId -> flash intensity 0..1
}

const MoldStructure: React.FC<MoldStructureProps> = ({
  focusWallId,
  focusProgress,
  wallFlashes,
}) => {
  const frame = useCurrentFrame();

  // Glow animation for walls after frame 300
  const finalGlow = interpolate(frame, [300, 360], [0, 0.3], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  const renderWall = (seg: WallSegment) => {
    const flash = wallFlashes[seg.id] || 0;
    const isFocused = seg.id === focusWallId;
    const labelBrightness = isFocused
      ? interpolate(focusProgress, [0, 1], [0.3, 1])
      : 0.3 + finalGlow;

    const wallOpacity = 0.4 + flash * 0.6 + finalGlow;
    const strokeW = WALL_STROKE + flash * 2;

    return (
      <g key={seg.id}>
        {/* Wall line */}
        <line
          x1={seg.x1}
          y1={seg.y1}
          x2={seg.x2}
          y2={seg.y2}
          stroke={WALL_COLOR}
          strokeWidth={strokeW}
          strokeLinecap="round"
          opacity={wallOpacity}
        />
        {/* Glow behind wall on flash */}
        {flash > 0.01 && (
          <line
            x1={seg.x1}
            y1={seg.y1}
            x2={seg.x2}
            y2={seg.y2}
            stroke={WALL_COLOR}
            strokeWidth={strokeW + 8}
            strokeLinecap="round"
            opacity={flash * 0.3}
            filter="url(#wallGlow)"
          />
        )}
        {/* Label */}
        <text
          x={seg.labelX}
          y={seg.labelY}
          fill={WALL_COLOR}
          opacity={labelBrightness}
          fontFamily={MONO_FONT}
          fontSize={9}
          textAnchor={seg.normalX > 0 ? 'end' : seg.normalX < 0 ? 'start' : 'middle'}
          dominantBaseline="middle"
        >
          {seg.label}
        </text>
      </g>
    );
  };

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="wallGlow">
          <feGaussianBlur stdDeviation="4" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Cavity fill */}
      <rect
        x={MOLD_LEFT}
        y={MOLD_TOP + 50}
        width={MOLD_RIGHT - MOLD_LEFT}
        height={MOLD_BOTTOM - MOLD_TOP - 50}
        fill={CAVITY_COLOR}
        rx={2}
      />

      {/* Nozzle */}
      <path
        d={`M ${NOZZLE_X - NOZZLE_WIDTH / 2} ${MOLD_TOP - 5}
            L ${NOZZLE_X - 15} ${MOLD_TOP + NOZZLE_HEIGHT}
            L ${NOZZLE_X + 15} ${MOLD_TOP + NOZZLE_HEIGHT}
            L ${NOZZLE_X + NOZZLE_WIDTH / 2} ${MOLD_TOP - 5} Z`}
        fill="none"
        stroke={WALL_COLOR_DIM}
        strokeWidth={3}
      />

      {/* Wall segments */}
      {WALL_SEGMENTS.map(renderWall)}
    </svg>
  );
};

export default MoldStructure;
