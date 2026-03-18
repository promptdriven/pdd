import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import { SPLIT, TIMING } from './constants';

export const SplitDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [TIMING.SPLIT_DRAW_START, TIMING.SPLIT_DRAW_START + TIMING.SPLIT_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const lineHeight = drawProgress * 1080;
  const yOffset = (1080 - lineHeight) / 2;

  return (
    <AbsoluteFill>
      <div
        style={{
          position: 'absolute',
          left: SPLIT.X - 1,
          top: yOffset,
          width: SPLIT.DIVIDER_WIDTH,
          height: lineHeight,
          backgroundColor: SPLIT.DIVIDER_COLOR,
          opacity: SPLIT.DIVIDER_OPACITY,
        }}
      />
    </AbsoluteFill>
  );
};
