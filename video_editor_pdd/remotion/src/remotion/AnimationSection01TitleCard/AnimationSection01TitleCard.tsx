import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION_TIMING } from './constants';
import { RadialGlow } from './RadialGlow';
import { TitleText } from './TitleText';
import { ExpandingRule } from './ExpandingRule';

export const AnimationSection01TitleCard: React.FC = () => {
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

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        opacity: backgroundOpacity,
      }}
    >
      <RadialGlow />
      {frame >= ANIMATION_TIMING.titleFadeStart && <TitleText />}
      {frame >= ANIMATION_TIMING.ruleFadeStart && <ExpandingRule />}
    </AbsoluteFill>
  );
};

export const defaultAnimationSection01TitleCardProps = {};

export default AnimationSection01TitleCard;
