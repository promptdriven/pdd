/**
 * VeoSection01OpeningTitleCard
 *
 * Opening title card for the VEO section with cinematic fade-in and particle effects
 * Duration: 3s (90 frames at 30fps)
 */

import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { ParticleSystem } from './ParticleSystem';
import { TitleCard } from './TitleCard';
import { UnderlineAccent } from './UnderlineAccent';
import { COLORS, TIMING, DIMENSIONS } from './constants';

export const VeoSection01OpeningTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Title scale and opacity animation (frames 0-20)
  const titleScale = interpolate(
    frame,
    [0, TIMING.titleFadeIn],
    [0.8, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const titleOpacity = interpolate(
    frame,
    [0, TIMING.titleFadeIn],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Underline draw animation (frames 20-40)
  const underlineWidth = interpolate(
    frame,
    [TIMING.titleFadeIn, TIMING.titleFadeIn + TIMING.underlineDraw],
    [0, DIMENSIONS.underline.width],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.background.top} 0%, ${COLORS.background.bottom} 100%)`,
        position: 'relative',
      }}
    >
      {/* Vignette overlay */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          background: 'radial-gradient(circle, transparent 30%, rgba(0, 0, 0, 0.3) 100%)',
        }}
      />

      {/* Particle system */}
      <ParticleSystem />

      {/* Main title */}
      <TitleCard
        text="VEO SECTION"
        scale={titleScale}
        opacity={titleOpacity}
      />

      {/* Underline accent */}
      <UnderlineAccent width={underlineWidth} />
    </AbsoluteFill>
  );
};

export default VeoSection01OpeningTitleCard;

export const defaultVeoSection01OpeningTitleCardProps = {};
