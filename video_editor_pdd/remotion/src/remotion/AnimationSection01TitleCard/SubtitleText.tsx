import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION_TIMING, TEXT, CANVAS } from './constants';

export const SubtitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, ANIMATION_TIMING.subtitleFadeEnd - ANIMATION_TIMING.subtitleFadeStart],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Position below the accent line
  const titleCenterY = CANVAS.height / 2 + DIMENSIONS.titleOffsetY;
  const titleHalfHeight = (TYPOGRAPHY.title.fontSize * 1.2) / 2;
  const accentLineTop = titleCenterY + titleHalfHeight + DIMENSIONS.accentLineGap;
  const top = accentLineTop + DIMENSIONS.accentLineHeight + DIMENSIONS.subtitleGap;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top,
        width: CANVAS.width,
        textAlign: 'center',
        fontFamily: TYPOGRAPHY.subtitle.fontFamily,
        fontSize: TYPOGRAPHY.subtitle.fontSize,
        fontWeight: TYPOGRAPHY.subtitle.fontWeight,
        color: COLORS.subtitleSlate,
        lineHeight: 1.5,
        opacity,
      }}
    >
      {TEXT.subtitle}
    </div>
  );
};
