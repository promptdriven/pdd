import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { GlowRing } from './GlowRing';
import { AnimatedCircle } from './AnimatedCircle';

export const AnimationSection02BlueCirclePulse: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      <GlowRing />
      <AnimatedCircle />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection02BlueCirclePulseProps = {};

export default AnimationSection02BlueCirclePulse;
