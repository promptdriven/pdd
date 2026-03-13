import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, useVideoConfig } from 'remotion';
import { COLORS, ANIMATION, resolveTitleCardLayout } from './constants';
import { TitleText } from './TitleText';
import { HorizontalRule } from './HorizontalRule';
import { SubtitleText } from './SubtitleText';
import { ParticleDrift } from './ParticleDrift';
import { VignetteOverlay } from './VignetteOverlay';

export const VeoSection01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();
  const layout = resolveTitleCardLayout(width, height);

  // Frame 0-10: Background gradient fades in from black
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
        {/* Particle drift — ambient background effect */}
        <ParticleDrift layout={layout} />

        {/* Title text: "VEO SECTION" — fades in frame 0-10 */}
        <TitleText layout={layout} />

        {/* Horizontal rule — expands frame 10-22, glow pulse 22-38 */}
        <HorizontalRule layout={layout} />

        {/* Subtitle: "AI-Generated Video Integration" — fades in frame 10-22 */}
        <SubtitleText layout={layout} />

        {/* Vignette — darkened edges */}
        <VignetteOverlay />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export const defaultVeoSection01TitleCardProps = {};

export default VeoSection01TitleCard;
