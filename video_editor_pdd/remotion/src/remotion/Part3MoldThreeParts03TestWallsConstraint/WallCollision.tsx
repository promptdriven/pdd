import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLLISION_EVENTS,
  WALL_SEGMENTS,
  WALL_COLOR,
  CollisionEvent,
} from './constants';

/**
 * Renders ripple effects at wall collision points.
 * Also computes and exposes current flash intensities via a render callback.
 */
interface WallCollisionProps {
  onFlashValues?: (flashes: Record<string, number>) => void;
}

const WallCollision: React.FC<WallCollisionProps> = () => {
  const frame = useCurrentFrame();

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      <defs>
        <filter id="rippleGlow">
          <feGaussianBlur stdDeviation="2" />
        </filter>
      </defs>
      {COLLISION_EVENTS.map((evt) => {
        const wall = WALL_SEGMENTS.find((w) => w.id === evt.wallId);
        if (!wall) return null;

        const elapsed = frame - evt.frame;
        if (elapsed < 0 || elapsed > evt.rippleDuration + 5) return null;

        // Ripple center: midpoint of wall segment
        const cx = (wall.x1 + wall.x2) / 2;
        const cy = (wall.y1 + wall.y2) / 2;

        // Ripple expand
        const rippleProgress = interpolate(
          elapsed,
          [0, evt.rippleDuration],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
        );

        const rippleOpacity = interpolate(
          elapsed,
          [0, evt.rippleDuration],
          [0.4, 0],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        const rippleR = 10 + rippleProgress * 50;

        // Determine if this is a vertical or horizontal wall
        const isVertical = wall.x1 === wall.x2;

        return (
          <g key={evt.wallId + '-' + evt.frame}>
            {/* Ripple arcs */}
            {[0, 0.3, 0.6].map((delay, i) => {
              const delayedProgress = Math.max(0, rippleProgress - delay);
              const r = 8 + delayedProgress * 60;
              const op = rippleOpacity * (1 - delay) * (delayedProgress > 0 ? 1 : 0);
              if (op < 0.01) return null;

              // Draw arc on the cavity side of the wall
              const offsetX = isVertical ? wall.normalX * r : 0;
              const offsetY = !isVertical ? wall.normalY * r : 0;

              return (
                <ellipse
                  key={i}
                  cx={cx + (isVertical ? wall.normalX * 5 : 0)}
                  cy={cy + (!isVertical ? wall.normalY * 5 : 0)}
                  rx={isVertical ? r * 0.4 : r}
                  ry={isVertical ? r : r * 0.4}
                  fill="none"
                  stroke={WALL_COLOR}
                  strokeWidth={1.5}
                  opacity={op}
                  filter="url(#rippleGlow)"
                />
              );
            })}

            {/* Impact burst */}
            {elapsed < 4 && (
              <circle
                cx={cx + (isVertical ? wall.normalX * 3 : 0)}
                cy={cy + (!isVertical ? wall.normalY * 3 : 0)}
                r={4 + elapsed * 3}
                fill={WALL_COLOR}
                opacity={interpolate(elapsed, [0, 4], [0.6, 0], {
                  extrapolateLeft: 'clamp',
                  extrapolateRight: 'clamp',
                })}
              />
            )}
          </g>
        );
      })}
    </svg>
  );
};

/**
 * Compute flash intensities for all walls at a given frame.
 * Used by the parent to pass to MoldStructure.
 */
export function getWallFlashes(frame: number): Record<string, number> {
  const flashes: Record<string, number> = {};
  for (const evt of COLLISION_EVENTS) {
    const elapsed = frame - evt.frame;
    if (elapsed >= 0 && elapsed <= evt.flashDuration) {
      const intensity = interpolate(elapsed, [0, evt.flashDuration], [1, 0], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.exp),
      });
      flashes[evt.wallId] = intensity;
    }
  }
  return flashes;
}

export default WallCollision;
