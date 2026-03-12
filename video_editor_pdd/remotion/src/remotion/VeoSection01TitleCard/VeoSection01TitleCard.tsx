import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, useVideoConfig } from 'remotion';
import { COLORS, ANIMATION, resolveTitleCardLayout } from './constants';
import { TitleText } from './TitleText';
import { HorizontalRule } from './HorizontalRule';
import { ParticleDrift } from './ParticleDrift';

export const VeoSection01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();
  const layout = resolveTitleCardLayout(width, height);

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
        <ParticleDrift layout={layout} />

        {/* Centered title text with parallax fade-in */}
        <TitleText layout={layout} />

        {/* Horizontal rule drawing outward from center */}
        <HorizontalRule layout={layout} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export const defaultVeoSection01TitleCardProps = {};

export default VeoSection01TitleCard;
