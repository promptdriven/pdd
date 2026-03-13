import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { GlowEffect } from './GlowEffect';
import { PulsingCircle } from './PulsingCircle';

export const AnimationSection02BlueCirclePulse: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(circle at center, ${COLORS.backgroundCenter} 0%, ${COLORS.backgroundEdge} 100%)`,
      }}
    >
      <GlowEffect />
      <PulsingCircle />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection02BlueCirclePulseProps = {};

export default AnimationSection02BlueCirclePulse;
