import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

const MOLD_ACCENT = '#D9944A';
const MOLD_WALL_OPACITY = 0.7;
const MOLD_WALL_STROKE = 4;
const GLOW_RADIUS = 8;
const CAVITY_BG = '#0F172A';

// Mold dimensions
const CX = 470;
const CY = 310;
const W = 340;
const H = 260;

interface WallSegment {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
}

const MOLD_WALLS: WallSegment[] = [
  // Outer rectangle
  { x1: CX - W / 2, y1: CY - H / 2, x2: CX + W / 2, y2: CY - H / 2 },
  { x1: CX + W / 2, y1: CY - H / 2, x2: CX + W / 2, y2: CY + H / 2 },
  { x1: CX + W / 2, y1: CY + H / 2, x2: CX - W / 2, y2: CY + H / 2 },
  { x1: CX - W / 2, y1: CY + H / 2, x2: CX - W / 2, y2: CY - H / 2 },
  // Internal channels
  { x1: CX - W / 4, y1: CY - H / 2, x2: CX - W / 4, y2: CY + H / 4 },
  { x1: CX + W / 4, y1: CY - H / 4, x2: CX + W / 4, y2: CY + H / 2 },
  { x1: CX - W / 4, y1: CY, x2: CX + W / 4, y2: CY },
];

// Injection entry at top center
const ENTRY_X = CX;
const ENTRY_Y = CY - H / 2;

interface MoldCavityProps {
  panelWidth: number;
  panelHeight: number;
}

export const MoldCavity: React.FC<MoldCavityProps> = ({
  panelWidth,
  panelHeight,
}) => {
  const frame = useCurrentFrame();

  // Walls draw in over frames 0-30
  const wallReveal = interpolate(frame, [0, 30], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
  });

  return (
    <svg
      width={panelWidth}
      height={panelHeight}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="wallGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation={GLOW_RADIUS} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Cavity interior fill */}
      <rect
        x={CX - W / 2}
        y={CY - H / 2}
        width={W}
        height={H}
        fill={CAVITY_BG}
        opacity={wallReveal}
        rx={4}
      />

      {/* Injection entry funnel */}
      <polygon
        points={`${ENTRY_X - 15},${ENTRY_Y - 30} ${ENTRY_X + 15},${ENTRY_Y - 30} ${ENTRY_X + 6},${ENTRY_Y} ${ENTRY_X - 6},${ENTRY_Y}`}
        fill={MOLD_ACCENT}
        opacity={MOLD_WALL_OPACITY * wallReveal}
      />

      {/* Wall segments */}
      {MOLD_WALLS.map((seg, i) => {
        // Stagger wall reveal
        const segDelay = i * 3;
        const segOpacity = interpolate(
          frame,
          [segDelay, segDelay + 15],
          [0, MOLD_WALL_OPACITY],
          {
            easing: Easing.out(Easing.quad),
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }
        );

        // Glow on contact — each wall segment glows at different times
        const contactDelay = 150 + i * 15;
        const segGlow = interpolate(
          frame,
          [contactDelay, contactDelay + 10],
          [0, 1],
          {
            easing: Easing.out(Easing.cubic),
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }
        );

        const currentOpacity = segOpacity + segGlow * (1 - segOpacity);

        return (
          <line
            key={`wall-${i}`}
            x1={seg.x1}
            y1={seg.y1}
            x2={seg.x2}
            y2={seg.y2}
            stroke={MOLD_ACCENT}
            strokeWidth={MOLD_WALL_STROKE}
            opacity={currentOpacity}
            strokeLinecap="round"
            filter={segGlow > 0.3 ? 'url(#wallGlow)' : undefined}
          />
        );
      })}
    </svg>
  );
};

export default MoldCavity;
