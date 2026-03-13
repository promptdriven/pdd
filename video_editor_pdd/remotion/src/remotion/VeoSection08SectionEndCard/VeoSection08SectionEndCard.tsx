import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { CompletionRing } from './CompletionRing';
import { CheckmarkIcon } from './CheckmarkIcon';
import { CompletionText } from './CompletionText';
import { ExpandingRule } from './ExpandingRule';
import { TaglineText } from './TaglineText';
import { FadeToBlack } from './FadeToBlack';

export const VeoSection08SectionEndCard: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.gradientTop} 0%, ${COLORS.gradientBottom} 100%)`,
      }}
    >
      {/* Circle outline draws itself (frames 0-8), fills with green tint (frames 8-16) */}
      <CompletionRing />

      {/* Check stroke draws inside circle (frames 8-16) */}
      <CheckmarkIcon />

      {/* "VEO SECTION COMPLETE" fades in + slides up (frames 16-22) */}
      <CompletionText />

      {/* Horizontal rule expands from center (frames 16-22) */}
      <ExpandingRule />

      {/* Tagline fades in (frames 22-28) */}
      <TaglineText />

      {/* Full-screen fade to black (frames 28-37) */}
      <FadeToBlack />
    </AbsoluteFill>
  );
};

export const defaultVeoSection08SectionEndCardProps = {};

export default VeoSection08SectionEndCard;
