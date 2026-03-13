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

  // Frame 0-15: Background gradient fades in from black (linear clamp)
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
        {/* Particle drift — runs continuously across full duration */}
        <ParticleDrift layout={layout} />

        {/* Centred title text with parallax fade-in */}
        <TitleText layout={layout} />

        {/* Horizontal rule drawing outward from centre */}
        <HorizontalRule layout={layout} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export const defaultVeoSection01TitleCardProps = {};

export default VeoSection01TitleCard;
