import React from 'react';
import { AbsoluteFill, Sequence, useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION_TIMINGS } from './constants';
import { ParticleSystem } from './ParticleSystem';
import { AccentLine } from './AccentLine';
import { TitleText } from './TitleText';
import { SubtitleText } from './SubtitleText';
import { NoiseOverlay } from './NoiseOverlay';

export const AnimationSection01OpeningTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fade-in animation
  const backgroundOpacity = interpolate(
    frame,
    [ANIMATION_TIMINGS.backgroundFadeIn.start, ANIMATION_TIMINGS.backgroundFadeIn.end],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(to bottom, ${COLORS.gradientTop}, ${COLORS.gradientBottom})`,
        opacity: backgroundOpacity,
      }}
    >
      {/* Noise texture overlay */}
      <NoiseOverlay />

      {/* Particle system - runs throughout entire sequence */}
      <Sequence from={0} durationInFrames={ANIMATION_TIMINGS.particlesDuration}>
        <ParticleSystem />
      </Sequence>

      {/* Accent line - starts at frame 15 */}
      <Sequence from={ANIMATION_TIMINGS.accentLine.start}>
        <AccentLine />
      </Sequence>

      {/* Main title - starts at frame 30 */}
      <Sequence from={ANIMATION_TIMINGS.title.start}>
        <TitleText />
      </Sequence>

      {/* Subtitle - starts at frame 45 */}
      <Sequence from={ANIMATION_TIMINGS.subtitle.start}>
        <SubtitleText />
      </Sequence>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection01OpeningTitleCardProps = {};

export default AnimationSection01OpeningTitleCard;
