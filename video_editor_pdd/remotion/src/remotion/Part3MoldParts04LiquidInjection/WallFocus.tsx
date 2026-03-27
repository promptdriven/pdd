import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WALLS,
  FOCUS_WALL_INDEX,
  WALL_GLOW_COLOR,
  RIPPLE_COLOR,
  RIPPLE_DURATION,
} from './constants';

/**
 * Renders the focus/zoom effect on the null → None wall.
 * Shows the wall pulsing, enhanced ripple, and label highlight.
 */
export const WallFocus: React.FC = () => {
  const frame = useCurrentFrame();
  const focusWall = WALLS[FOCUS_WALL_INDEX];

  // Pulse the label on contact (frame 200 relative to parent)
  // The parent Sequence starts at 180, so local frame 20 = global 200
  const localHitFrame = focusWall.hitFrame - 180; // 200 - 180 = 20
  const pulseProgress = interpolate(
    frame,
    [localHitFrame, localHitFrame + 15, localHitFrame + 30],
    [1, 1.4, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Wall glow brightens on contact
  const glowOpacity = interpolate(
    frame,
    [localHitFrame, localHitFrame + 15],
    [0.5, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Enhanced ripple for focus wall
  const rippleElapsed = frame - localHitFrame;
  const showRipple = rippleElapsed >= 0 && rippleElapsed <= RIPPLE_DURATION * 2;

  const midY = focusWall.y + focusWall.height / 2;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
      viewBox="0 0 1920 1080"
    >
      <defs>
        <filter id="focus-glow">
          <feGaussianBlur stdDeviation="10" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Enhanced wall glow */}
      <rect
        x={focusWall.x - 6}
        y={focusWall.y - 4}
        width={12}
        height={focusWall.height + 8}
        fill={WALL_GLOW_COLOR}
        opacity={glowOpacity}
        filter="url(#focus-glow)"
        rx={3}
      />

      {/* Pulsing label */}
      <text
        x={focusWall.x}
        y={focusWall.y - 20}
        textAnchor="middle"
        fill={WALL_GLOW_COLOR}
        fontFamily="JetBrains Mono, monospace"
        fontSize={14 * pulseProgress}
        fontWeight="bold"
        opacity={Math.min(1, glowOpacity + 0.2)}
      >
        {focusWall.label}
      </text>

      {/* Enhanced ripple arcs */}
      {showRipple &&
        [0, 1, 2, 3, 4].map((i) => {
          const rippleProgress = interpolate(
            rippleElapsed,
            [i * 2, RIPPLE_DURATION * 2],
            [0, 1],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
          );
          const radius = 10 + rippleProgress * 50;
          const arcOpacity = 0.35 * (1 - rippleProgress);

          return (
            <ellipse
              key={i}
              cx={focusWall.x - 20}
              cy={midY}
              rx={radius}
              ry={radius * 0.5}
              fill="none"
              stroke={RIPPLE_COLOR}
              strokeWidth={2.5 - rippleProgress * 1.5}
              opacity={arcOpacity}
            />
          );
        })}
    </svg>
  );
};
