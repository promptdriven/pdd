import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { GradientMesh } from './GradientMesh';
import { WaveformVisualizer } from './WaveformVisualizer';
import { WordByWordReveal } from './WordByWordReveal';
import { VoiceBadge } from './VoiceBadge';

export const VeoSection07NarrationOverlayIntro: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      <GradientMesh />
      <WaveformVisualizer />
      <WordByWordReveal />
      <VoiceBadge />
    </AbsoluteFill>
  );
};

export const defaultVeoSection07NarrationOverlayIntroProps = {};

export default VeoSection07NarrationOverlayIntro;
