import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, ANIMATION_TIMING, CANVAS } from './constants';
import { ParticleSystem } from './ParticleSystem';
import { AnimatedCheckmark } from './AnimatedCheckmark';
import { ExpandingRule } from './ExpandingRule';

export const AnimationSection08SectionClosingCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fade-in: frames 0-10
  const backgroundOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.bgFadeStart, ANIMATION_TIMING.bgFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Tagline fade-in: frames 15-30
  const taglineOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.taglineFadeStart, ANIMATION_TIMING.taglineFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Card fade-out: frames 35-45
  const cardFadeOut = interpolate(
    frame,
    [ANIMATION_TIMING.cardFadeOutStart, ANIMATION_TIMING.cardFadeOutEnd],
    [1, 0.7],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // Combined opacity: background fade-in * card fade-out
  const combinedOpacity = backgroundOpacity * cardFadeOut;

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.gradientTop} 0%, ${COLORS.gradientBottom} 100%)`,
        opacity: combinedOpacity,
      }}
    >
      {/* Faint background particles */}
      <ParticleSystem />

      {/* Animated checkmark */}
      <AnimatedCheckmark />

      {/* Tagline text */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: POSITIONS.taglineY,
          width: CANVAS.width,
          textAlign: 'center',
          opacity: taglineOpacity,
          fontFamily: TYPOGRAPHY.tagline.fontFamily,
          fontSize: TYPOGRAPHY.tagline.fontSize,
          fontWeight: TYPOGRAPHY.tagline.fontWeight,
          letterSpacing: TYPOGRAPHY.tagline.letterSpacing,
          textTransform: TYPOGRAPHY.tagline.textTransform,
          color: COLORS.taglineText,
        }}
      >
        SECTION COMPLETE
      </div>

      {/* Expanding horizontal rule */}
      <ExpandingRule />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection08SectionClosingCardProps = {};

export default AnimationSection08SectionClosingCard;
