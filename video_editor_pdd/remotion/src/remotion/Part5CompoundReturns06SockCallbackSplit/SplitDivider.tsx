import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  SPLIT_X,
  SPLIT_LINE_WIDTH,
  SPLIT_LINE_COLOR,
  SPLIT_LINE_OPACITY,
  HEIGHT,
  SPLIT_LINE_DRAW_START,
  SPLIT_LINE_DRAW_DURATION,
  REALIZATION_FLASH_START,
  GLOW_COLOR,
  GLOW_LINE_PEAK_OPACITY,
  GLOW_LINE_DURATION,
} from './constants';

export const SplitDivider: React.FC = () => {
  const frame = useCurrentFrame();

  // Split line draws top-to-bottom
  const lineHeight = interpolate(
    frame,
    [SPLIT_LINE_DRAW_START, SPLIT_LINE_DRAW_START + SPLIT_LINE_DRAW_DURATION],
    [0, HEIGHT],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Glow effect during realization moment
  const glowOpacity = interpolate(
    frame,
    [
      REALIZATION_FLASH_START,
      REALIZATION_FLASH_START + GLOW_LINE_DURATION / 2,
      REALIZATION_FLASH_START + GLOW_LINE_DURATION,
    ],
    [0, GLOW_LINE_PEAK_OPACITY, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <>
      {/* Main split line */}
      <div
        style={{
          position: 'absolute',
          left: SPLIT_X - SPLIT_LINE_WIDTH / 2,
          top: 0,
          width: SPLIT_LINE_WIDTH,
          height: lineHeight,
          backgroundColor: SPLIT_LINE_COLOR,
          opacity: SPLIT_LINE_OPACITY,
        }}
      />
      {/* Glow overlay on the split line */}
      {glowOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            left: SPLIT_X - 4,
            top: 0,
            width: 8,
            height: HEIGHT,
            backgroundColor: GLOW_COLOR,
            opacity: glowOpacity,
            filter: 'blur(4px)',
          }}
        />
      )}
    </>
  );
};
