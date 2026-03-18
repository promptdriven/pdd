import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { TYPOGRAPHY } from './constants';

interface AnimatedLineProps {
  text: string;
  startFrame: number;
  duration: number;
  slideDistance: number;
  fontSize: number;
  fontWeight: number;
  color: string;
  opacity: number;
  y: number;
}

/**
 * AnimatedLine renders a single text line with fade-in + upward slide animation.
 */
export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  text,
  startFrame,
  duration,
  slideDistance,
  fontSize,
  fontWeight,
  color,
  opacity: targetOpacity,
  y,
}) => {
  const frame = useCurrentFrame();

  const fadeOpacity = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, targetOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const translateY = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [slideDistance, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: y,
        left: 0,
        width: 1920,
        display: 'flex',
        justifyContent: 'center',
        opacity: fadeOpacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.FONT_FAMILY,
          fontSize,
          fontWeight,
          color,
          lineHeight: 1.4,
        }}
      >
        {text}
      </span>
    </div>
  );
};
