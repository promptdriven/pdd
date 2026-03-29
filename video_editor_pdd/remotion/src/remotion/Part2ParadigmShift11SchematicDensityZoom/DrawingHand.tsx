import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  HAND_COLOR,
  HAND_OPACITY,
  HAND_FADE_START,
  HAND_FADE_DURATION,
} from './constants';

/**
 * Stylised drawing hand with pencil that decelerates and fades out.
 * The hand "draws" by oscillating horizontally, slowing over time.
 */
const DrawingHand: React.FC = () => {
  const frame = useCurrentFrame();

  // Speed factor: 1 → 0 over 0..270 (easeOutCubic deceleration)
  const speed = interpolate(frame, [0, 270], [1, 0], {
    easing: Easing.out(Easing.poly(3)),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Opacity: full → 0 at fade
  const opacity = interpolate(
    frame,
    [HAND_FADE_START, HAND_FADE_START + HAND_FADE_DURATION],
    [HAND_OPACITY, 0],
    {
      easing: Easing.in(Easing.poly(2)),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Horizontal oscillation (drawing motion)
  const oscillation = Math.sin(frame * 0.3) * 30 * speed;
  // Vertical drift (small)
  const drift = Math.cos(frame * 0.17) * 12 * speed;

  // Hand position – starts near centre, drifts
  const handX = 960 + oscillation + frame * 0.2 * speed;
  const handY = 540 + drift - frame * 0.15 * speed;

  if (opacity <= 0.01) return null;

  return (
    <svg
      width={1920}
      height={1080}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        pointerEvents: 'none',
      }}
    >
      <g
        transform={`translate(${handX}, ${handY})`}
        opacity={opacity}
      >
        {/* Pencil */}
        <line
          x1={0}
          y1={0}
          x2={-40}
          y2={-55}
          stroke={HAND_COLOR}
          strokeWidth={4}
          strokeLinecap="round"
        />
        {/* Pencil tip */}
        <polygon
          points="0,0 -6,-8 6,-8"
          fill={HAND_COLOR}
          transform="rotate(35)"
        />
        {/* Simplified hand silhouette */}
        <ellipse
          cx={-30}
          cy={-50}
          rx={22}
          ry={14}
          fill={HAND_COLOR}
          opacity={0.6}
          transform="rotate(-15, -30, -50)"
        />
        {/* Thumb */}
        <ellipse
          cx={-14}
          cy={-35}
          rx={8}
          ry={5}
          fill={HAND_COLOR}
          opacity={0.5}
          transform="rotate(20, -14, -35)"
        />
        {/* Fingers wrapped */}
        <ellipse
          cx={-42}
          cy={-44}
          rx={10}
          ry={6}
          fill={HAND_COLOR}
          opacity={0.45}
          transform="rotate(-25, -42, -44)"
        />
      </g>
    </svg>
  );
};

export default DrawingHand;
