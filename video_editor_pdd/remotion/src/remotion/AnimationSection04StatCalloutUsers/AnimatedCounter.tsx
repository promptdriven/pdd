/**
 * AnimatedCounter component
 * Large number that counts up from 0 to target value with formatting
 */

import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, POSITIONS, TYPOGRAPHY, ANIMATION } from './constants';

export const AnimatedCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Counter animation with easeOutQuart
  const progress = interpolate(
    frame,
    [0, ANIMATION.COUNTER_DURATION],
    [0, 1],
    {
      extrapolateRight: 'clamp',
      easing: Easing.poly(4), // quartic easing
    }
  );

  const currentValue = Math.floor(progress * ANIMATION.TARGET_VALUE);

  // Format with commas
  const formattedValue = currentValue.toLocaleString('en-US');

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.COUNTER.X,
        top: POSITIONS.COUNTER.Y,
        transform: 'translate(-50%, -50%)',
        fontFamily: TYPOGRAPHY.COUNTER.FAMILY,
        fontSize: TYPOGRAPHY.COUNTER.SIZE,
        fontWeight: TYPOGRAPHY.COUNTER.WEIGHT,
        color: COLORS.COUNTER,
        fontFeatureSettings: '"tnum"',
        lineHeight: 1,
        textAlign: 'center',
      }}
    >
      {formattedValue}
    </div>
  );
};
