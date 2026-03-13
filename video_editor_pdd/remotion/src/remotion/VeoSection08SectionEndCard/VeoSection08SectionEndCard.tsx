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

  // Frame 0-10: Content fades in over the gradient background
  // Background gradient is always visible (non-black) from frame 0.
  const contentOpacity = interpolate(
    frame,
    [ANIMATION.backgroundFadeStart, ANIMATION.backgroundFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.gradientTop} 0%, ${COLORS.gradientBottom} 100%)`,
      }}
    >
      {/* Bokeh particles — drift continuously from frame 0, visible immediately */}
      <BokehParticles layout={layout} />

      <AbsoluteFill style={{ opacity: contentOpacity }}>
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
