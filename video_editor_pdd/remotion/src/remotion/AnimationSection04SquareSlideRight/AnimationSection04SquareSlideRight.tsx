import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { GuideLine } from './GuideLine';
import { MotionTrail } from './MotionTrail';
import { SlidingSquare } from './SlidingSquare';
import { SquareGlow } from './SquareGlow';

export const AnimationSection04SquareSlideRight: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      <GuideLine />
      <SquareGlow />
      <MotionTrail />
      <SlidingSquare />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection04SquareSlideRightProps = {};

export default AnimationSection04SquareSlideRight;
