import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION, DIMENSIONS } from './constants';

export const SubtitleText: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 18–26: Fade in opacity 0→1, easeOutCubic
  const opacity = interpolate(
    frame,
    [ANIMATION.subtitleFadeStart, ANIMATION.subtitleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Frame 18–26: Slide up from +10px → 0px
  const translateY = interpolate(
    frame,
    [ANIMATION.subtitleFadeStart, ANIMATION.subtitleFadeEnd],
    [ANIMATION.subtitleShiftPx, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Position: below title + rule
  // Title bottom: 40% * 1080 + 56 * 1.2 = 432 + 67.2 = ~499px
  // Rule: +20px gap + 2px height = ~521px
  // Subtitle: +30px gap below rule = ~551px
  const titleBottomPx = DIMENSIONS.titleTopPercent * 1080 + TYPOGRAPHY.title.fontSize * 1.2;
  const ruleBottom = titleBottomPx + DIMENSIONS.ruleGap + DIMENSIONS.ruleHeight;
  const subtitleTop = ruleBottom + DIMENSIONS.subtitleGap;

  return (
    <div
      style={{
        position: 'absolute',
        top: subtitleTop,
        left: 0,
        width: '100%',
        display: 'flex',
        justifyContent: 'center',
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.subtitle.fontFamily,
          fontSize: TYPOGRAPHY.subtitle.fontSize,
          fontWeight: TYPOGRAPHY.subtitle.fontWeight,
          color: COLORS.subtitleText,
        }}
      >
        AI-Generated Cinematic Footage
      </span>
    </div>
  );
};
