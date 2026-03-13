import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, type TitleCardLayout } from './constants';

export const HorizontalRule: React.FC<{ layout: TitleCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  // Frame 10-22: Scale outward from centre with easeInOutQuad
  const scaleX = interpolate(
    frame,
    [ANIMATION.ruleFadeStart, ANIMATION.ruleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  // Frame 22-38: Ambient glow pulse (opacity 0.8 → 1.0 → 0.8)
  const glowProgress = interpolate(
    frame,
    [ANIMATION.glowPulseStart, ANIMATION.glowPulseEnd],
    [0, Math.PI * 2],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );
  const glowOpacity = frame >= ANIMATION.glowPulseStart
    ? 0.8 + 0.2 * Math.sin(glowProgress)
    : 1;

  return (
    <div
      style={{
        position: 'absolute',
        top: layout.dimensions.ruleY,
        left: layout.width / 2 - layout.dimensions.ruleWidth / 2,
        width: layout.dimensions.ruleWidth,
        height: layout.dimensions.ruleHeight,
        backgroundColor: COLORS.rule,
        transform: `scaleX(${scaleX})`,
        transformOrigin: 'center',
        opacity: glowOpacity,
        boxShadow: `0 0 ${8 * glowOpacity}px ${COLORS.rule}`,
      }}
    />
  );
};
