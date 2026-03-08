import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, TYPOGRAPHY, POSITIONS, ANIMATION_TIMING } from './constants';
import { BokehParticles } from './BokehParticles';
import { CompletionRing } from './CompletionRing';
import { ExpandingRule } from './ExpandingRule';

export const VeoSection08SectionEndCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Title "Veo Section" fades in with upward drift
  const titleOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.titleFadeStart, ANIMATION_TIMING.titleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  const titleTranslateY = interpolate(
    frame,
    [ANIMATION_TIMING.titleFadeStart, ANIMATION_TIMING.titleFadeEnd],
    [16, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Subtitle "COMPLETE" fades in
  const subtitleOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.subtitleFadeStart, ANIMATION_TIMING.subtitleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Card fade-out near end
  const cardFadeOut = interpolate(
    frame,
    [ANIMATION_TIMING.cardFadeOutStart, ANIMATION_TIMING.cardFadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.gradientTop} 0%, ${COLORS.gradientBottom} 100%)`,
        opacity: cardFadeOut,
      }}
    >
      {/* Warm bokeh particles drifting */}
      <BokehParticles />

      {/* Animated completion ring with checkmark */}
      <CompletionRing />

      {/* Title text */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: POSITIONS.titleY,
          width: CANVAS.width,
          textAlign: 'center',
          opacity: titleOpacity,
          transform: `translateY(${titleTranslateY}px)`,
          fontFamily: TYPOGRAPHY.title.fontFamily,
          fontSize: TYPOGRAPHY.title.fontSize,
          fontWeight: TYPOGRAPHY.title.fontWeight,
          letterSpacing: TYPOGRAPHY.title.letterSpacing,
          color: COLORS.titleText,
        }}
      >
        Veo Section
      </div>

      {/* Subtitle */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: POSITIONS.subtitleY,
          width: CANVAS.width,
          textAlign: 'center',
          opacity: subtitleOpacity,
          fontFamily: TYPOGRAPHY.subtitle.fontFamily,
          fontSize: TYPOGRAPHY.subtitle.fontSize,
          fontWeight: TYPOGRAPHY.subtitle.fontWeight,
          letterSpacing: TYPOGRAPHY.subtitle.letterSpacing,
          textTransform: TYPOGRAPHY.subtitle.textTransform,
          color: COLORS.subtitleText,
        }}
      >
        COMPLETE
      </div>

      {/* Expanding horizontal rule */}
      <ExpandingRule />
    </AbsoluteFill>
  );
};

export const defaultVeoSection08SectionEndCardProps = {};

export default VeoSection08SectionEndCard;
