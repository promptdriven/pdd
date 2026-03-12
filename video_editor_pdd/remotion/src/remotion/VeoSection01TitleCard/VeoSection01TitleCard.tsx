import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION } from './constants';
import { TitleText } from './TitleText';
import { HorizontalRule } from './HorizontalRule';
import { ParticleDrift } from './ParticleDrift';

export const VeoSection01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background gradient fades in from black over frames 0-15
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
    <AbsoluteFill
      style={{
        backgroundColor: '#0B1D3A',
      }}
    >
      <AbsoluteFill
        style={{
          opacity: backgroundOpacity,
        }}
      >
        {/* Deep ocean-blue gradient background */}
        <AbsoluteFill
          style={{
            background: `linear-gradient(180deg, ${COLORS.gradientTop} 0%, ${COLORS.gradientBottom} 100%)`,
          }}
        />

        {/* Particle drift layer — runs continuously across full duration */}
        <ParticleDrift />

        {/* Centered title text with parallax fade-in */}
        <TitleText />

        {/* Horizontal rule drawing outward from center */}
        <HorizontalRule />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export const defaultVeoSection01TitleCardProps = {};

export default VeoSection01TitleCard;
