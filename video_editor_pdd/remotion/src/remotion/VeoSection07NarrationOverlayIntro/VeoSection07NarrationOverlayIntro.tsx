import React from 'react';
import { AbsoluteFill, useVideoConfig } from 'remotion';
import { GradientMesh } from './GradientMesh';
import { WaveformVisualizer } from './WaveformVisualizer';
import { WordByWordReveal } from './WordByWordReveal';
import { VoiceBadge } from './VoiceBadge';

export const VeoSection07NarrationOverlayIntro: React.FC = () => {
  const { width, height } = useVideoConfig();

  return (
    <AbsoluteFill
      style={{
        width,
        height,
        backgroundColor: 'transparent',
        pointerEvents: 'none',
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
