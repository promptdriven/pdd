import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { AMBER, GREEN } from './constants';

/**
 * A small mold cross-section icon showing a new wall being added.
 * Appears in the PDD panel to illustrate the mold tightening.
 */
export const MiniMold: React.FC<{ appearFrame: number; x: number; y: number }> = ({
  appearFrame,
  x,
  y,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [appearFrame, appearFrame + 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  if (progress <= 0) return null;

  const newWallHeight = interpolate(progress, [0, 1], [0, 60]);

  return (
    <div
      style={{
        position: 'absolute',
        left: x - 40,
        top: y - 50,
        width: 80,
        height: 100,
        opacity: 0.4 * progress,
      }}
    >
      <svg width={80} height={100} viewBox="0 0 80 100">
        {/* Outer mold walls */}
        <rect x={2} y={5} width={76} height={90} rx={4} fill="none" stroke={GREEN} strokeWidth={1.5} opacity={0.5} />

        {/* Existing inner walls */}
        <line x1={25} y1={10} x2={25} y2={90} stroke={GREEN} strokeWidth={1} opacity={0.4} />
        <line x1={55} y1={10} x2={55} y2={90} stroke={GREEN} strokeWidth={1} opacity={0.4} />
        <line x1={10} y1={50} x2={70} y2={50} stroke={GREEN} strokeWidth={1} opacity={0.4} />

        {/* New wall being added (amber, animates in) */}
        <line
          x1={40}
          y1={50 - newWallHeight / 2}
          x2={40}
          y2={50 + newWallHeight / 2}
          stroke={AMBER}
          strokeWidth={2}
          opacity={0.8}
        />

        {/* Glow on new wall */}
        <line
          x1={40}
          y1={50 - newWallHeight / 2}
          x2={40}
          y2={50 + newWallHeight / 2}
          stroke={AMBER}
          strokeWidth={6}
          opacity={0.15 * progress}
        />

        {/* Small label */}
        <text
          x={40}
          y={98}
          textAnchor="middle"
          fontSize={7}
          fill={AMBER}
          opacity={0.6 * progress}
          fontFamily="Inter, sans-serif"
        >
          null check wall
        </text>
      </svg>
    </div>
  );
};
