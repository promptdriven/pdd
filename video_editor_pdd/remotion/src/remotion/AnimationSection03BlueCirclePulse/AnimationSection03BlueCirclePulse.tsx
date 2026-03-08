import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { Vignette } from './Vignette';
import { GlowHalo } from './GlowHalo';
import { ScalingCircle } from './ScalingCircle';
import { RippleRing } from './RippleRing';

export const AnimationSection03BlueCirclePulse: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      <Vignette />
      <GlowHalo />
      <ScalingCircle />
      <RippleRing />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection03BlueCirclePulseProps = {};

export default AnimationSection03BlueCirclePulse;
