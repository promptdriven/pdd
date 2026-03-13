import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, type TitleCardLayout } from './constants';

export const SubtitleText: React.FC<{ layout: TitleCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  // Frame 10-22: Fade in with easeOutQuad
  const opacity = interpolate(
    frame,
    [ANIMATION.subtitleFadeStart, ANIMATION.subtitleFadeEnd],
    [0, layout.dimensions.subtitleOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: layout.dimensions.subtitleY,
        left: 0,
        width: layout.width,
        display: 'flex',
        justifyContent: 'center',
      }}
    >
      <span
        style={{
          fontFamily: layout.typography.subtitle.fontFamily,
          fontSize: layout.typography.subtitle.fontSize,
          fontWeight: layout.typography.subtitle.fontWeight,
          letterSpacing: layout.typography.subtitle.letterSpacing,
          color: COLORS.subtitleText,
          opacity,
        }}
      >
        AI-Generated Video Integration
      </span>
    </div>
  );
};
