import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, CANVAS, ANIMATION, DIMENSIONS } from './constants';

export const LightStreak: React.FC = () => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [ANIMATION.lightStreakStart, ANIMATION.lightStreakEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Only render during the sweep window
  if (frame < ANIMATION.lightStreakStart) return null;

  const xPos = progress * (CANVAS.width + 200) - 100;

  return (
    <>
      {/* Main streak line */}
      <div
        style={{
          position: 'absolute',
          top: CANVAS.height / 2,
          left: 0,
          width: CANVAS.width,
          height: DIMENSIONS.lightStreakHeight,
          background: `linear-gradient(90deg, transparent 0%, ${COLORS.accent}99 ${Math.max(0, progress * 100 - 10)}%, ${COLORS.accent} ${progress * 100}%, transparent ${Math.min(100, progress * 100 + 2)}%)`,
          opacity: 0.6,
        }}
      />
      {/* Bright leading glow */}
      <div
        style={{
          position: 'absolute',
          top: CANVAS.height / 2 - 15,
          left: xPos - 40,
          width: 80,
          height: 30,
          borderRadius: '50%',
          background: `radial-gradient(ellipse, ${COLORS.accent}80 0%, transparent 70%)`,
          opacity: progress < 1 ? 0.8 : 0,
        }}
      />
    </>
  );
};
