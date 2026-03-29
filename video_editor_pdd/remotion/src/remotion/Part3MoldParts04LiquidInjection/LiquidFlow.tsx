import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  LIQUID_LEADING_EDGE,
  LIQUID_LEADING_OPACITY,
  LIQUID_GRADIENT_FROM,
  LIQUID_GRADIENT_TO,
  LIQUID_BLUR,
  LIQUID_PATH_POINTS,
  WALLS,
  RIPPLE_COLOR,
  RIPPLE_FRAMES,
} from './constants';

/**
 * Interpolate position along the liquid path for a given frame.
 */
function getLiquidHeadPosition(frame: number): { x: number; y: number } | null {
  if (frame < LIQUID_PATH_POINTS[0].frame) return null;

  for (let i = 0; i < LIQUID_PATH_POINTS.length - 1; i++) {
    const curr = LIQUID_PATH_POINTS[i];
    const next = LIQUID_PATH_POINTS[i + 1];
    if (frame >= curr.frame && frame <= next.frame) {
      const t = (frame - curr.frame) / (next.frame - curr.frame);
      // Smooth easing for organic feel
      const eased = t * t * (3 - 2 * t); // smoothstep
      return {
        x: curr.x + (next.x - curr.x) * eased,
        y: curr.y + (next.y - curr.y) * eased,
      };
    }
  }

  // Past last point — return final position
  const last = LIQUID_PATH_POINTS[LIQUID_PATH_POINTS.length - 1];
  return { x: last.x, y: last.y };
}

/**
 * Build the SVG path string for liquid that has been "poured" up to the current frame.
 */
function buildLiquidPath(frame: number): string {
  const points: Array<{ x: number; y: number }> = [];

  for (let i = 0; i < LIQUID_PATH_POINTS.length; i++) {
    const pt = LIQUID_PATH_POINTS[i];
    if (frame < pt.frame) {
      // Interpolate to current position
      const head = getLiquidHeadPosition(frame);
      if (head) points.push(head);
      break;
    }
    points.push({ x: pt.x, y: pt.y });
  }

  if (points.length < 2) return '';

  // Build smooth bezier curve through points
  let d = `M ${points[0].x} ${points[0].y}`;
  for (let i = 1; i < points.length; i++) {
    const prev = points[i - 1];
    const curr = points[i];
    const cpx1 = prev.x + (curr.x - prev.x) * 0.4;
    const cpy1 = prev.y + (curr.y - prev.y) * 0.1;
    const cpx2 = prev.x + (curr.x - prev.x) * 0.6;
    const cpy2 = prev.y + (curr.y - prev.y) * 0.9;
    d += ` C ${cpx1} ${cpy1}, ${cpx2} ${cpy2}, ${curr.x} ${curr.y}`;
  }

  return d;
}

/**
 * Ripple effect at a wall hit point.
 */
const WallRipple: React.FC<{
  cx: number;
  cy: number;
  hitFrame: number;
}> = ({ cx, cy, hitFrame }) => {
  const frame = useCurrentFrame();
  const elapsed = frame - hitFrame;

  if (elapsed < 0 || elapsed > RIPPLE_FRAMES + 5) return null;

  const arcs = [0, 1, 2].map((i) => {
    const delay = i * 3;
    const rippleElapsed = elapsed - delay;
    if (rippleElapsed < 0) return null;

    const radius = interpolate(rippleElapsed, [0, RIPPLE_FRAMES], [4, 30 + i * 12], {
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    });
    const opacity = interpolate(rippleElapsed, [0, RIPPLE_FRAMES], [0.3, 0], {
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    });

    return (
      <circle
        key={i}
        cx={cx}
        cy={cy}
        r={radius}
        fill="none"
        stroke={RIPPLE_COLOR}
        strokeWidth={2}
        opacity={opacity}
      />
    );
  });

  return <>{arcs}</>;
};

export const LiquidFlow: React.FC = () => {
  const frame = useCurrentFrame();
  const liquidPath = buildLiquidPath(frame);
  const head = getLiquidHeadPosition(frame);

  // Calculate how much of the fill we've completed (0 to 1)
  const lastPoint = LIQUID_PATH_POINTS[LIQUID_PATH_POINTS.length - 1];
  const fillProgress = interpolate(frame, [0, lastPoint.frame], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Liquid body width grows as it fills
  const bodyWidth = interpolate(fillProgress, [0, 1], [6, 14], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute' }}
        viewBox="0 0 1920 1080"
      >
        <defs>
          <linearGradient id="liquidGrad" x1="0%" y1="0%" x2="0%" y2="100%">
            <stop offset="0%" stopColor={LIQUID_GRADIENT_FROM} />
            <stop offset="100%" stopColor={LIQUID_GRADIENT_TO} />
          </linearGradient>
          <filter id="liquidGlow" x="-20%" y="-20%" width="140%" height="140%">
            <feGaussianBlur in="SourceGraphic" stdDeviation={LIQUID_BLUR} />
          </filter>
          <filter id="leadingEdgeGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur in="SourceGraphic" stdDeviation={6} />
          </filter>
        </defs>

        {/* Liquid body - glow layer */}
        {liquidPath && (
          <path
            d={liquidPath}
            fill="none"
            stroke="url(#liquidGrad)"
            strokeWidth={bodyWidth + 8}
            strokeLinecap="round"
            strokeLinejoin="round"
            opacity={0.3}
            filter="url(#liquidGlow)"
          />
        )}

        {/* Liquid body - main layer */}
        {liquidPath && (
          <path
            d={liquidPath}
            fill="none"
            stroke="url(#liquidGrad)"
            strokeWidth={bodyWidth}
            strokeLinecap="round"
            strokeLinejoin="round"
            opacity={0.85}
          />
        )}

        {/* Liquid body - bright center */}
        {liquidPath && (
          <path
            d={liquidPath}
            fill="none"
            stroke={LIQUID_GRADIENT_FROM}
            strokeWidth={Math.max(2, bodyWidth * 0.3)}
            strokeLinecap="round"
            strokeLinejoin="round"
            opacity={0.5}
          />
        )}

        {/* Leading edge bright point */}
        {head && frame >= 0 && frame <= lastPoint.frame && (
          <>
            <circle
              cx={head.x}
              cy={head.y}
              r={12}
              fill={LIQUID_LEADING_EDGE}
              opacity={LIQUID_LEADING_OPACITY * 0.3}
              filter="url(#leadingEdgeGlow)"
            />
            <circle
              cx={head.x}
              cy={head.y}
              r={5}
              fill={LIQUID_LEADING_EDGE}
              opacity={LIQUID_LEADING_OPACITY}
            />
          </>
        )}

        {/* Ripples at wall contact points */}
        {WALLS.map((wall) => {
          const rippleCx = wall.width > wall.height
            ? wall.x + wall.width / 2
            : wall.x;
          const rippleCy = wall.width > wall.height
            ? wall.y
            : wall.y + wall.height / 2;
          return (
            <WallRipple
              key={wall.id}
              cx={rippleCx}
              cy={rippleCy}
              hitFrame={wall.hitFrame}
            />
          );
        })}

        {/* Filled area blobs at each reached waypoint for volume */}
        {LIQUID_PATH_POINTS.map((pt, i) => {
          if (frame < pt.frame) return null;
          const elapsed = frame - pt.frame;
          const blobRadius = interpolate(elapsed, [0, 30], [0, 18 + i * 2], {
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });
          return (
            <circle
              key={`blob-${i}`}
              cx={pt.x}
              cy={pt.y}
              r={blobRadius}
              fill="url(#liquidGrad)"
              opacity={0.25}
            />
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};
