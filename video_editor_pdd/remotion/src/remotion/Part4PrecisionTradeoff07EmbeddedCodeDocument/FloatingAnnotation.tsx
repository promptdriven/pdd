import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, FONTS } from './constants';

interface FloatingAnnotationProps {
  startFrame: number;
  y: number;
}

export const FloatingAnnotation: React.FC<FloatingAnnotationProps> = ({
  startFrame,
  y,
}) => {
  const frame = useCurrentFrame();
  const elapsed = Math.max(0, frame - startFrame);

  // Fade in with easeOut(quad) over 20 frames
  const opacity = interpolate(elapsed, [0, 20], [0, 0.6], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
    extrapolateLeft: 'clamp',
  });

  const translateY = interpolate(elapsed, [0, 20], [8, 0], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
    extrapolateLeft: 'clamp',
  });

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
      <span
        style={{
          fontFamily: FONTS.sans,
          fontSize: 14,
          color: COLORS.annotationText,
        }}
      >
        Stay in{' '}
        <span style={{ color: COLORS.intentLabel }}>prompt space</span>{' '}
        as long as possible. Dip into{' '}
        <span style={{ color: COLORS.codeLabel }}>code</span>{' '}
        when you must.
      </span>
    </div>
  );
};
