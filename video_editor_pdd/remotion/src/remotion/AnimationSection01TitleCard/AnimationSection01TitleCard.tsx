import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION_TIMING } from './constants';
import { ParticleSystem } from './ParticleSystem';
import { TitleText } from './TitleText';
import { AccentLine } from './AccentLine';
import { SubtitleText } from './SubtitleText';

export const AnimationSection01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fade-in animation
  const backgroundOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.backgroundFadeStart, ANIMATION_TIMING.backgroundFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.gradientTop} 0%, ${COLORS.gradientBottom} 100%)`,
        opacity: backgroundOpacity,
      }}
    >
      {/* Subtle noise texture overlay */}
      <AbsoluteFill
        style={{
          opacity: 0.05,
          backgroundImage: `url("data:image/svg+xml,%3Csvg viewBox='0 0 400 400' xmlns='http://www.w3.org/2000/svg'%3E%3Cfilter id='noiseFilter'%3E%3CfeTurbulence type='fractalNoise' baseFrequency='0.9' numOctaves='4' /%3E%3C/filter%3E%3Crect width='100%25' height='100%25' filter='url(%23noiseFilter)' /%3E%3C/svg%3E")`,
        }}
      />

      {/* Particle system */}
      <ParticleSystem />

      {/* Main title */}
      {frame >= ANIMATION_TIMING.titleSlideStart && <TitleText />}

      {/* Accent line */}
      {frame >= ANIMATION_TIMING.accentLineStart && <AccentLine />}

      {/* Subtitle */}
      {frame >= ANIMATION_TIMING.subtitleFadeStart && <SubtitleText />}
    </AbsoluteFill>
  );
};

export const defaultAnimationSection01TitleCardProps = {};

export default AnimationSection01TitleCard;
