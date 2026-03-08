import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION_TIMING } from './constants';
import { FilmGrainOverlay } from './FilmGrainOverlay';
import { BokehField } from './BokehField';
import { TitleText } from './TitleText';
import { GoldenRule } from './GoldenRule';

export const VeoSection01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background gradient fades from black over frames 0-12
  const backgroundOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.backgroundFadeStart, ANIMATION_TIMING.backgroundFadeEnd],
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
        opacity: backgroundOpacity,
      }}
    >
      {/* Film grain texture overlay */}
      <FilmGrainOverlay />

      {/* Warm bokeh circles drifting diagonally */}
      <BokehField />

      {/* Title text: "Veo Section" with upward fade-in */}
      <TitleText />

      {/* Golden horizontal rule drawing outward from center */}
      <GoldenRule />
    </AbsoluteFill>
  );
};

export const defaultVeoSection01TitleCardProps = {};

export default VeoSection01TitleCard;
