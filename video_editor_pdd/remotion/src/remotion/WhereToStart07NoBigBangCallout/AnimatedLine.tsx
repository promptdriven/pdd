import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface AnimatedLineProps {
  /** Frame at which the animation begins */
  startFrame: number;
  /** Duration of the fade+slide animation in frames */
  duration: number;
  /** Upward slide distance in pixels */
  slideDistance: number;
  /** Y position (center of text) */
  y: number;
  children: React.ReactNode;
}

/**
 * Animates children with a combined fade-in and upward slide.
 * Uses easeOut(cubic) easing for a smooth deceleration.
 */
export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  startFrame,
  duration,
  slideDistance,
  y,
  children,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const opacity = progress;
  const translateY = interpolate(progress, [0, 1], [slideDistance, 0]);

  return (
    <div
      style={{
        position: 'absolute',
        top: y,
        left: 0,
        right: 0,
        display: 'flex',
        justifyContent: 'center',
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      {children}
    </div>
  );
};
