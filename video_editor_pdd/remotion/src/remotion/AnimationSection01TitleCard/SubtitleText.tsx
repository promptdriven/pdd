import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, ANIMATION_TIMING } from './constants';

export const SubtitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.subtitleFadeStart, ANIMATION_TIMING.subtitleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        right: 0,
        top: POSITIONS.subtitleY,
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        opacity,
      }}
    >
      <p
        style={{
          fontFamily: TYPOGRAPHY.subtitle.fontFamily,
          fontSize: TYPOGRAPHY.subtitle.fontSize,
          fontWeight: TYPOGRAPHY.subtitle.fontWeight,
          letterSpacing: TYPOGRAPHY.subtitle.letterSpacing,
          color: COLORS.subtitleText,
          margin: 0,
        }}
      >
        Integration Test Video
      </p>
    </div>
  );
};
