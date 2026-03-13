import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION_TIMING } from './constants';
import { RadialGlow } from './RadialGlow';
import { StaggeredText } from './StaggeredText';
import { ExpandingDivider } from './ExpandingDivider';

export const AnimationSection01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 0-5: Background fades in from black
  const backgroundOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.backgroundFadeStart, ANIMATION_TIMING.backgroundFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#000000' }}>
      <AbsoluteFill
        style={{
          backgroundColor: COLORS.background,
          opacity: backgroundOpacity,
        }}
      >
        <RadialGlow />
        <StaggeredText />
        <ExpandingDivider />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection01TitleCardProps = {};

export default AnimationSection01TitleCard;
