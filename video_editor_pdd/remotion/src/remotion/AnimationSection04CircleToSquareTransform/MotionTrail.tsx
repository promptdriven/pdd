import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { SHAPE, TRAIL, TIMING, COLORS } from './constants';

/**
 * Renders ghost copies trailing behind the moving shape.
 * Each copy is offset further back along the X axis with decreasing opacity.
 */
export const MotionTrail: React.FC = () => {
  const frame = useCurrentFrame();

  // Current shape position (same calc as main shape)
  const currentX = interpolate(
    frame,
    [TIMING.slideStart, TIMING.slideEnd],
    [SHAPE.startX, SHAPE.endX],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.poly(4) },
  );

  // Current border-radius
  const currentRadius = interpolate(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [SHAPE.startBorderRadius, SHAPE.endBorderRadius],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.65, 0, 0.35, 1) },
  );

  // Current color as interpolated rgb
  const colorProgress = interpolate(
    frame,
    [TIMING.colorStart, TIMING.colorEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Interpolate RGB channels: #3B82F6 → #22C55E
  const r = Math.round(59 + (34 - 59) * colorProgress);
  const g = Math.round(130 + (197 - 130) * colorProgress);
  const b = Math.round(246 + (94 - 246) * colorProgress);
  const currentColor = `rgb(${r}, ${g}, ${b})`;

  // Trail only visible during and after slide
  const trailVisibility = interpolate(
    frame,
    [TIMING.slideStart, TIMING.slideStart + 5, TIMING.settleStart, TIMING.settleEnd],
    [0, 1, 1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  if (trailVisibility <= 0) return null;

  return (
    <>
      {TRAIL.opacities.map((baseOpacity, i) => {
        const trailX = currentX - TRAIL.spacing * (i + 1);
        const opacity = baseOpacity * trailVisibility;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              width: SHAPE.size,
              height: SHAPE.size,
              left: trailX - SHAPE.size / 2,
              top: SHAPE.cy - SHAPE.size / 2,
              borderRadius: currentRadius,
              backgroundColor: currentColor,
              opacity,
            }}
          />
        );
      })}
    </>
  );
};
