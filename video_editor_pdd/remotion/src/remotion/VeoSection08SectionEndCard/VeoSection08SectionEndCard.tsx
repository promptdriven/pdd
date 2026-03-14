import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { AnimatedCheckmark } from './AnimatedCheckmark';
import { TitleText } from './TitleText';
import { HorizontalRule } from './HorizontalRule';
import { SubtitleText } from './SubtitleText';

export const VeoSection08SectionEndCard: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Checkmark icon: scales in with bounce (frames 0-8), path draws simultaneously */}
      <AnimatedCheckmark />

      {/* "Veo Section Complete" fades in + slides up (frames 8-14) */}
      <TitleText />

      {/* Gold horizontal rule expands from center (frames 14-18) */}
      <HorizontalRule />

      {/* "2 Veo clips · 3 Remotion overlays" fades in (frames 18-22) */}
      <SubtitleText />
    </AbsoluteFill>
  );
};

export const defaultVeoSection08SectionEndCardProps = {};

export default VeoSection08SectionEndCard;
