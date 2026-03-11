import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION_TIMING } from './constants';
import { ParticleBackground } from './ParticleBackground';
import { ExpandingRule } from './ExpandingRule';
import { SectionCompleteText } from './SectionCompleteText';
import { DecorativeShapes } from './DecorativeShapes';

export const AnimationSection07SectionClosingCard: React.FC = () => {
  const frame = useCurrentFrame();

  const backgroundOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.backgroundFadeStart, ANIMATION_TIMING.backgroundFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.fadeOutStart, ANIMATION_TIMING.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  const combinedOpacity = Math.min(backgroundOpacity, fadeOutOpacity);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: '#00FF00',
      }}
    >
      <AbsoluteFill
        style={{
          backgroundColor: COLORS.background,
          opacity: combinedOpacity,
        }}
      >
        <ParticleBackground />
        <ExpandingRule />
        {frame >= ANIMATION_TIMING.textFadeStart && <SectionCompleteText />}
        {frame >= ANIMATION_TIMING.circlePopStart && <DecorativeShapes />}
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection07SectionClosingCardProps = {};

export default AnimationSection07SectionClosingCard;
