import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { ScalingCircle } from './ScalingCircle';
import { PulseRing } from './PulseRing';

export const AnimationSection02BlueCirclePulse: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      <ScalingCircle />
      <PulseRing />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection02BlueCirclePulseProps = {};

export default AnimationSection02BlueCirclePulse;
