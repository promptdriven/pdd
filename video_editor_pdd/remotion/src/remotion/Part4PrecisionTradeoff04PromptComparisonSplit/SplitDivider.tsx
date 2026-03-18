import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { CANVAS_HEIGHT, COLORS, SPLIT_X } from './constants';

export const SplitDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const lineHeight = interpolate(frame, [0, 15], [0, CANVAS_HEIGHT], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: SPLIT_X - 1,
        top: 0,
        width: 2,
        height: lineHeight,
        backgroundColor: COLORS.splitLine,
        opacity: 0.25,
      }}
    />
  );
};
