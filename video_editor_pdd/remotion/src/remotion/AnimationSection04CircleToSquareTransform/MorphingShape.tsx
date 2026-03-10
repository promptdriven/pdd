import React from 'react';
import { useCurrentFrame, interpolate, spring, Easing } from 'remotion';
import { SHAPE, TIMING, COLORS } from './constants';

/**
 * The main shape that morphs from a circle to a rounded square,
 * transitions color, slides right, and settles with a bounce.
 */
export const MorphingShape: React.FC = () => {
  const frame = useCurrentFrame();

  // 1. Border-radius morph (circle → square)
  const borderRadius = interpolate(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [SHAPE.startBorderRadius, SHAPE.endBorderRadius],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.65, 0, 0.35, 1) },
  );

  // 2. Color transition (blue → green, linear)
  const colorProgress = interpolate(
    frame,
    [TIMING.colorStart, TIMING.colorEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Interpolate RGB: #EC4899 (236,72,153) → #22C55E (34,197,94)
  const r = Math.round(236 + (34 - 236) * colorProgress);
  const g = Math.round(72 + (197 - 72) * colorProgress);
  const b = Math.round(153 + (94 - 153) * colorProgress);
  const fillColor = `rgb(${r}, ${g}, ${b})`;

  // 3. Horizontal slide
  const slideX = interpolate(
    frame,
    [TIMING.slideStart, TIMING.slideEnd],
    [SHAPE.startX, SHAPE.endX],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.poly(4) },
  );

  // 4. Settle bounce (spring)
  const settleFrame = Math.max(0, frame - TIMING.settleStart);
  const settleScale = spring({
    frame: settleFrame,
    fps: 30,
    config: { damping: 15, stiffness: 120 },
    from: 1.05,
    to: 1.0,
    durationInFrames: TIMING.settleEnd - TIMING.settleStart,
  });

  // Only apply scale bounce after settle starts
  const scale = frame >= TIMING.settleStart ? settleScale : 1.0;

  return (
    <div
      style={{
        position: 'absolute',
        width: SHAPE.size,
        height: SHAPE.size,
        left: slideX - SHAPE.size / 2,
        top: SHAPE.cy - SHAPE.size / 2,
        borderRadius,
        backgroundColor: fillColor,
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
      }}
    />
  );
};
