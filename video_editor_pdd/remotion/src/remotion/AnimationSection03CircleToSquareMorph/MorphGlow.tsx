import React from 'react';
import { useCurrentFrame, interpolate, interpolateColors, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TIMING, MORPH } from './constants';

export const MorphGlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Glow color transitions in sync with the morph
  const glowColor = interpolateColors(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [COLORS.fromShape, COLORS.toShape]
  );

  // Glow opacity: 25% during morph, settles to 20%
  const glowOpacity = interpolate(
    frame,
    [TIMING.morphStart, TIMING.morphEnd, TIMING.totalDuration],
    [MORPH.glowOpacityMorph, MORPH.glowOpacityMorph, MORPH.glowOpacitySettle],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.linear,
    }
  );

  // Size tracks the shape size loosely (slightly larger for glow spread)
  const glowSize = interpolate(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [DIMENSIONS.fromSize + 60, DIMENSIONS.toSize + 60],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Border-radius morphs along with the shape
  const glowBorderRadius = interpolate(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [50, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        width: glowSize,
        height: glowSize,
        borderRadius: `${glowBorderRadius}%`,
        backgroundColor: glowColor,
        opacity: glowOpacity,
        filter: `blur(${DIMENSIONS.glowBlur}px)`,
        top: '50%',
        left: '50%',
        transform: 'translate(-50%, -50%)',
      }}
    />
  );
};
