import React from 'react';
import { AbsoluteFill, useVideoConfig } from 'remotion';
import { BlurredBackground } from './BlurredBackground';
import { WordByWordText } from './WordByWordText';
import { WaveformVisualizer } from './WaveformVisualizer';
import { AccentUnderline } from './AccentUnderline';

export const VeoSection07NarrationOverlayIntro: React.FC = () => {
  const { width, height } = useVideoConfig();

  return (
    <AbsoluteFill
      style={{
        backgroundColor: 'transparent',
        width,
        height,
        pointerEvents: 'none',
      }}
    >
      {/* Blurred Veo footage still + dark overlay — fades in frame 0–4 */}
      <BlurredBackground />

      {/* Words appear one at a time with fade-up — frame 4–18 */}
      <WordByWordText />

      {/* 40 waveform bars with traveling wave pulse — frame 10+ */}
      <WaveformVisualizer />

      {/* Gold accent underline grows from center — frame 18–22 */}
      <AccentUnderline />
    </AbsoluteFill>
  );
};

export const defaultVeoSection07NarrationOverlayIntroProps = {};

export default VeoSection07NarrationOverlayIntro;
