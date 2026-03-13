import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING, CANVAS, TYPOGRAPHY } from './constants';

export const AccentLine: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [0, ANIMATION_TIMING.accentLineEnd - ANIMATION_TIMING.accentLineStart],
    [0, DIMENSIONS.accentLineEndWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  const centerX = CANVAS.width / 2;
  const left = centerX - width / 2;

  // Position below the title: canvas center + titleOffsetY + half title height + gap
  const titleCenterY = CANVAS.height / 2 + DIMENSIONS.titleOffsetY;
  const titleHalfHeight = (TYPOGRAPHY.title.fontSize * 1.2) / 2;
  const top = titleCenterY + titleHalfHeight + DIMENSIONS.accentLineGap;

  return (
    <div
      style={{
        position: 'absolute',
        left,
        top,
        width,
        height: DIMENSIONS.accentLineHeight,
        backgroundColor: COLORS.accentLine,
      }}
    />
  );
};
