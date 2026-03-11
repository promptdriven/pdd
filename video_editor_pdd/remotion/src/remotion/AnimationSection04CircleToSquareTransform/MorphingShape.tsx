import React from 'react';
import { useCurrentFrame, interpolate, spring, Easing } from 'remotion';
import { SHAPE, TIMING, COLORS } from './constants';

const CIRCLE_CLIP = [50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50];
const STAR_CLIP = [50, 0, 61, 35, 98, 35, 68, 57, 79, 91, 50, 70, 21, 91, 32, 57, 2, 35, 39, 35];

/**
 * The main shape that morphs from a circle to a star,
 * transitions color, slides right, and settles with a bounce.
 */
export const MorphingShape: React.FC = () => {
  const frame = useCurrentFrame();

  // 1. Clip-path morph (circle → star)
  const clipPoints = CIRCLE_CLIP.map((circleVal, i) => {
    return interpolate(
      frame,
      [TIMING.morphStart, TIMING.morphEnd],
      [circleVal, STAR_CLIP[i]],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.65, 0, 0.35, 1) },
    );
  });

  const clipPath = `polygon(${clipPoints[0]}% ${clipPoints[1]}%, ${clipPoints[2]}% ${clipPoints[3]}%, ${clipPoints[4]}% ${clipPoints[5]}%, ${clipPoints[6]}% ${clipPoints[7]}%, ${clipPoints[8]}% ${clipPoints[9]}%, ${clipPoints[10]}% ${clipPoints[11]}%, ${clipPoints[12]}% ${clipPoints[13]}%, ${clipPoints[14]}% ${clipPoints[15]}%, ${clipPoints[16]}% ${clipPoints[17]}%, ${clipPoints[18]}% ${clipPoints[19]}%)`;

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
        clipPath,
        backgroundColor: fillColor,
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
      }}
    />
  );
};
