import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  MOLD_WALLS,
  MOLD_BLUE,
  PURPLE_ACCENT,
  WALL_TRANSITION_START,
  WALL_TRANSITION_END,
} from './constants';

/**
 * Simplified mold cross-section rendered as SVG wall segments.
 * Proven walls transition from blue to purple during the specified frame range.
 */
export const MoldCrossSection: React.FC<{ dimOpacity: number }> = ({
  dimOpacity,
}) => {
  const frame = useCurrentFrame();

  return (
    <svg
      width={620}
      height={700}
      viewBox="0 0 620 700"
      style={{
        position: 'absolute',
        left: 0,
        top: 150,
        opacity: dimOpacity,
      }}
    >
      {/* Outer casing glow */}
      <rect
        x={80}
        y={160}
        width={460}
        height={480}
        rx={8}
        fill="none"
        stroke={MOLD_BLUE}
        strokeWidth={1}
        opacity={0.15}
      />

      {/* Cavity fill */}
      <rect
        x={120}
        y={200}
        width={380}
        height={400}
        rx={4}
        fill={MOLD_BLUE}
        opacity={0.05}
      />

      {/* Wall segments */}
      {MOLD_WALLS.map((wall, i) => {
        const transitionProgress = wall.proven
          ? interpolate(
              frame,
              [WALL_TRANSITION_START, WALL_TRANSITION_END],
              [0, 1],
              {
                extrapolateLeft: 'clamp',
                extrapolateRight: 'clamp',
                easing: Easing.inOut(Easing.sin),
              }
            )
          : 0;

        // Interpolate RGB channels from blue to purple
        const r = Math.round(74 + (167 - 74) * transitionProgress);
        const g = Math.round(144 + (139 - 144) * transitionProgress);
        const b = Math.round(217 + (250 - 217) * transitionProgress);
        const wallColor = `rgb(${r}, ${g}, ${b})`;

        const glowOpacity = wall.proven ? 0.15 + transitionProgress * 0.2 : 0.08;

        return (
          <g key={i}>
            {/* Glow behind wall */}
            <line
              x1={wall.x1}
              y1={wall.y1}
              x2={wall.x2}
              y2={wall.y2}
              stroke={wall.proven && transitionProgress > 0 ? PURPLE_ACCENT : MOLD_BLUE}
              strokeWidth={12}
              opacity={glowOpacity}
              strokeLinecap="round"
            />
            {/* Main wall line */}
            <line
              x1={wall.x1}
              y1={wall.y1}
              x2={wall.x2}
              y2={wall.y2}
              stroke={wallColor}
              strokeWidth={4}
              opacity={0.8}
              strokeLinecap="round"
            />
          </g>
        );
      })}

      {/* Internal channel indicators */}
      <circle cx={200} cy={400} r={6} fill={MOLD_BLUE} opacity={0.2} />
      <circle cx={430} cy={350} r={6} fill={MOLD_BLUE} opacity={0.2} />
      <circle cx={310} cy={450} r={4} fill={MOLD_BLUE} opacity={0.15} />
    </svg>
  );
};
