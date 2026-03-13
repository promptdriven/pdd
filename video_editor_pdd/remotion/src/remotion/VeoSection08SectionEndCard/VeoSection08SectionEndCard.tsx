import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, useVideoConfig } from 'remotion';
import { COLORS, ANIMATION, resolveEndCardLayout } from './constants';
import { BokehParticles } from './BokehParticles';
import { CompletionRing } from './CompletionRing';
import { CheckmarkIcon } from './CheckmarkIcon';
import { SectionLabel } from './SectionLabel';
import { ExpandingRule } from './ExpandingRule';

export const VeoSection08SectionEndCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();
  const layout = resolveEndCardLayout(width, height);

  // Frame 0-10: Background gradient fades in (opacity 0 → 1)
  const backgroundOpacity = interpolate(
    frame,
    [ANIMATION.backgroundFadeStart, ANIMATION.backgroundFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#000000' }}>
      <AbsoluteFill
        style={{
          background: `linear-gradient(180deg, ${COLORS.gradientTop} 0%, ${COLORS.gradientBottom} 100%)`,
          opacity: backgroundOpacity,
        }}
      >
        {/* Bokeh particles — drift continuously across full duration */}
        <BokehParticles layout={layout} />

        {/* Completion ring draws clockwise */}
        <CompletionRing layout={layout} />

        {/* Checkmark icon pops in with bounce */}
        <CheckmarkIcon layout={layout} />

        {/* Section label fades in */}
        <SectionLabel layout={layout} />

        {/* Horizontal rule expands outward from centre */}
        <ExpandingRule layout={layout} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export const defaultVeoSection08SectionEndCardProps = {};

export default VeoSection08SectionEndCard;
