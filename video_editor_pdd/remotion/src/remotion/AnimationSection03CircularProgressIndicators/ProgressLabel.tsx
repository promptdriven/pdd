/**
 * ProgressLabel component - renders label text below progress indicators
 */

import React from 'react';
import { interpolate, useCurrentFrame, useVideoConfig, Easing } from 'remotion';
import { TYPOGRAPHY } from './constants';

interface ProgressLabelProps {
  position: [number, number];
  label: string;
  duration: number;
}

export const ProgressLabel: React.FC<ProgressLabelProps> = ({
  position,
  label,
  duration,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Fade in with easeInOutQuad
  const opacity = interpolate(
    frame,
    [0, duration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  const [x, y] = position;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        transform: 'translate(-50%, 0)',
        fontFamily: TYPOGRAPHY.label.fontFamily,
        fontWeight: TYPOGRAPHY.label.fontWeight,
        fontSize: TYPOGRAPHY.label.fontSize,
        color: TYPOGRAPHY.label.color,
        textAlign: 'center',
        opacity,
      }}
    >
      {label}
    </div>
  );
};
