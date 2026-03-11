import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { SHAPE, TRAIL, TIMING, COLORS } from './constants';

const CIRCLE_CLIP = [50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50];
const STAR_CLIP = [50, 0, 61, 35, 98, 35, 68, 57, 79, 91, 50, 70, 21, 91, 32, 57, 2, 35, 39, 35];

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

  // Current clip-path (circle → star)
  const clipPoints = CIRCLE_CLIP.map((circleVal, i) => {
    return interpolate(
      frame,
      [TIMING.morphStart, TIMING.morphEnd],
      [circleVal, STAR_CLIP[i]],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.65, 0, 0.35, 1) },
    );
  });

  const clipPath = `polygon(${clipPoints[0]}% ${clipPoints[1]}%, ${clipPoints[2]}% ${clipPoints[3]}%, ${clipPoints[4]}% ${clipPoints[5]}%, ${clipPoints[6]}% ${clipPoints[7]}%, ${clipPoints[8]}% ${clipPoints[9]}%, ${clipPoints[10]}% ${clipPoints[11]}%, ${clipPoints[12]}% ${clipPoints[13]}%, ${clipPoints[14]}% ${clipPoints[15]}%, ${clipPoints[16]}% ${clipPoints[17]}%, ${clipPoints[18]}% ${clipPoints[19]}%)`;

  // Current color as interpolated rgb
  const colorProgress = interpolate(
    frame,
    [TIMING.colorStart, TIMING.colorEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Interpolate RGB channels: #EC4899 → #22C55E
  const r = Math.round(236 + (34 - 236) * colorProgress);
  const g = Math.round(72 + (197 - 72) * colorProgress);
  const b = Math.round(153 + (94 - 153) * colorProgress);
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
              clipPath,
              backgroundColor: currentColor,
              opacity,
            }}
          />
        );
      })}
    </>
  );
};
