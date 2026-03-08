/**
 * SuffixText component
 * "Active Users" text with fade in animation
 */

import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, POSITIONS, TYPOGRAPHY } from './constants';

export const SuffixText: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in
  const opacity = interpolate(
    frame,
    [0, 20],
    [0, 1],
    {
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.ease),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.SUFFIX.X,
        top: POSITIONS.SUFFIX.Y,
        transform: 'translate(-50%, -50%)',
        fontFamily: TYPOGRAPHY.SUFFIX.FAMILY,
        fontSize: TYPOGRAPHY.SUFFIX.SIZE,
        fontWeight: TYPOGRAPHY.SUFFIX.WEIGHT,
        color: COLORS.SUFFIX,
        opacity,
        textAlign: 'center',
      }}
    >
      Active Users
    </div>
  );
};
