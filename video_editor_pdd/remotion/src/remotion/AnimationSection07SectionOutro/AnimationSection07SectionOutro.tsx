import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { DrawCheckmark } from './DrawCheckmark';
import { CompleteText } from './CompleteText';
import { FadeToBlack } from './FadeToBlack';

export const AnimationSection07SectionOutro: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      <DrawCheckmark />
      <CompleteText />
      <FadeToBlack />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection07SectionOutroProps = {};

export default AnimationSection07SectionOutro;
