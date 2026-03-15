import React from 'react';
import { AbsoluteFill, OffthreadVideo, staticFile } from 'remotion';
import { useVisualMediaSrc } from '../_shared/visual-runtime';
import { COLORS } from './constants';
import { FrostedPanel } from './FrostedPanel';
import { GoldAccentLine } from './GoldAccentLine';
import { TypewriterCaption } from './TypewriterCaption';
import { WaveformVisualizer } from './WaveformVisualizer';

export const VeoSection07NarrationOverlayIntro: React.FC = () => {
  const backgroundSrc = useVisualMediaSrc(
    'backgroundSrc',
    'veo/05_veo_cutaway.mp4',
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Background Veo footage continuing underneath */}
      {backgroundSrc ? (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile(backgroundSrc)}
            style={{ width: '100%', height: '100%', objectFit: 'cover' }}
            startFrom={51}
            muted
          />
        </AbsoluteFill>
      ) : null}

      {/* Lower-third frosted glass panel with narration overlay */}
      <FrostedPanel>
        <GoldAccentLine />
        <TypewriterCaption />
        <WaveformVisualizer />
      </FrostedPanel>
    </AbsoluteFill>
  );
};

export const defaultVeoSection07NarrationOverlayIntroProps = {};

export default VeoSection07NarrationOverlayIntro;
