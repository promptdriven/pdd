import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION, DIMENSIONS } from './constants';

export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 10–18: Expand width from 0→320px, center-anchored, easeInOutCubic
  const width = interpolate(
    frame,
    [ANIMATION.ruleExpandStart, ANIMATION.ruleExpandEnd],
    [0, DIMENSIONS.ruleMaxWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  // Frame 26–51: Gentle ambient glow pulse (opacity 0.8–1.0 cycle), easeInOutSine
  const glowOpacity = frame >= ANIMATION.glowPulseStart
    ? interpolate(
        (frame - ANIMATION.glowPulseStart) % 25,
        [0, 12, 25],
        [0.8, 1.0, 0.8],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        },
      )
    : 1;

  // Position: 40% from top + title line-height offset + 20px gap
  const titleBottomPx = DIMENSIONS.titleTopPercent * 1080 + TYPOGRAPHY.title.fontSize * 1.2;
  const ruleTop = titleBottomPx + DIMENSIONS.ruleGap;

  return (
    <div
      style={{
        position: 'absolute',
        top: ruleTop,
        left: '50%',
        transform: 'translateX(-50%)',
        width,
        height: DIMENSIONS.ruleHeight,
        backgroundColor: COLORS.rule,
        opacity: glowOpacity,
        boxShadow: `0 0 12px ${COLORS.rule}`,
      }}
    />
  );
};
