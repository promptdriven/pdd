import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { CHART_CONFIG, ANIMATION_TIMING } from './constants';

export const ChartTitle: React.FC = () => {
  const frame = useCurrentFrame();
  const { typography } = CHART_CONFIG;
  const { start, duration } = ANIMATION_TIMING.labelsFadeIn;

  const opacity = interpolate(frame, [start, start + duration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.ease),
  });

  const scale = interpolate(frame, [start, start + duration], [0.8, 1.0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.ease),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: typography.title.x,
        top: typography.title.y,
        fontFamily: typography.title.fontFamily,
        fontWeight: typography.title.fontWeight,
        fontSize: typography.title.fontSize,
        color: typography.title.color,
        opacity,
        transform: `scale(${scale})`,
        transformOrigin: 'left center',
      }}
    >
      Exponential Growth 2024-2025
    </div>
  );
};
