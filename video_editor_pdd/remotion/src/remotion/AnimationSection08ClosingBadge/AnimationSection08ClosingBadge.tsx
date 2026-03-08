import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { RadialSpotlight } from './RadialSpotlight';
import { MonogramStroke } from './MonogramStroke';
import { ProgressRing } from './ProgressRing';
import { TypewriterText } from './TypewriterText';

export const AnimationSection08ClosingBadge: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Subtle radial spotlight */}
      <RadialSpotlight />

      {/* Progress ring around monogram */}
      <ProgressRing />

      {/* Monogram "R" with stroke draw + gradient fill + glow */}
      <MonogramStroke />

      {/* Typewriter brand name */}
      <TypewriterText />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection08ClosingBadgeProps = {};

export default AnimationSection08ClosingBadge;
