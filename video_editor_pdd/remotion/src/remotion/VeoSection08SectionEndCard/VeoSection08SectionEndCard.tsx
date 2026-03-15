import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { AnimatedCheckmark } from './AnimatedCheckmark';
import { TitleText } from './TitleText';
import { HorizontalRule } from './HorizontalRule';
import { FadeToBlack } from './FadeToBlack';

export const VeoSection08SectionEndCard: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Checkmark icon: circle draws frames 6-12, check draws frames 12-16 */}
      <AnimatedCheckmark />

      {/* "Veo Section Complete" fades in + slides up (frames 16-24) */}
      <TitleText />

      {/* Gold horizontal rule expands from center (frames 24-30) */}
      <HorizontalRule />

      {/* Gentle fade to black in final 10 frames (41-51) */}
      <FadeToBlack />
    </AbsoluteFill>
  );
};

export const defaultVeoSection08SectionEndCardProps = {};

export default VeoSection08SectionEndCard;
