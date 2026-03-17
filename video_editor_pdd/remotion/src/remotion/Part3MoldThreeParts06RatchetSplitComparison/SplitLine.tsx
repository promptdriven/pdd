import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { SPLIT_X, SPLIT_LINE_COLOR, HEIGHT } from './constants';

export const SplitLine: React.FC = () => {
  const frame = useCurrentFrame();

  const lineHeight = interpolate(frame, [0, 15], [0, HEIGHT], {
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
        backgroundColor: SPLIT_LINE_COLOR,
        opacity: 0.25,
      }}
    />
  );
};
