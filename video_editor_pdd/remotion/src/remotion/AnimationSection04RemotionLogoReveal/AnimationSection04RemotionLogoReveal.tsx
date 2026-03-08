import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { LogoGlow } from './LogoGlow';
import { LogoRing } from './LogoRing';
import { LogoTriangle } from './LogoTriangle';
import { TitleText } from './TitleText';

export const defaultAnimationSection04RemotionLogoRevealProps = {};

export const AnimationSection04RemotionLogoReveal: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Radial glow behind the logo */}
      <LogoGlow />

      {/* Animated ring that draws in */}
      <LogoRing />

      {/* Play-button triangle scales up */}
      <LogoTriangle />

      {/* Title and subtitle text */}
      <TitleText />
    </AbsoluteFill>
  );
};

export default AnimationSection04RemotionLogoReveal;
