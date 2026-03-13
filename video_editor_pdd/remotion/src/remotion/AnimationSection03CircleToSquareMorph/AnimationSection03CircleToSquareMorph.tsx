import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { MorphGlow } from './MorphGlow';
import { MorphShape } from './MorphShape';

export const AnimationSection03CircleToSquareMorph: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      <MorphGlow />
      <MorphShape />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection03CircleToSquareMorphProps = {};

export default AnimationSection03CircleToSquareMorph;
