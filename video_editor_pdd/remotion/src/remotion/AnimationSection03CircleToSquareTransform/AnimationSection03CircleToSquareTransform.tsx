import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { MorphShape } from './MorphShape';
import { GhostTrail } from './GhostTrail';

export const AnimationSection03CircleToSquareTransform: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      <GhostTrail />
      <MorphShape />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection03CircleToSquareTransformProps = {};

export default AnimationSection03CircleToSquareTransform;
