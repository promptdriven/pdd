/**
 * PrefixText component
 * "Over" text with fade in and scale animation
 */

import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, POSITIONS, TYPOGRAPHY } from './constants';

export const PrefixText: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in with slight scale
  const opacity = interpolate(
    frame,
    [0, 15],
    [0, 1],
    {
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.ease),
    }
  );

  const scale = interpolate(
    frame,
    [0, 15],
    [0.9, 1],
    {
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.ease),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.PREFIX.X,
        top: POSITIONS.PREFIX.Y,
        transform: `translate(-50%, -50%) scale(${scale})`,
        fontFamily: TYPOGRAPHY.PREFIX.FAMILY,
        fontSize: TYPOGRAPHY.PREFIX.SIZE,
        fontWeight: TYPOGRAPHY.PREFIX.WEIGHT,
        color: COLORS.PREFIX,
        opacity,
        textAlign: 'center',
      }}
    >
      Over
    </div>
  );
};
