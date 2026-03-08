import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { ShapeGlow } from './ShapeGlow';
import { MotionTrail } from './MotionTrail';
import { MorphingShape } from './MorphingShape';

export const defaultAnimationSection04CircleToSquareTransformProps = {};

export const AnimationSection04CircleToSquareTransform: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Glow layer (behind everything) */}
      <ShapeGlow />

      {/* Motion trail ghost copies */}
      <MotionTrail />

      {/* Main morphing shape */}
      <MorphingShape />
    </AbsoluteFill>
  );
};

export default AnimationSection04CircleToSquareTransform;
