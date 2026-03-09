import React from 'react';
import { AbsoluteFill } from 'remotion';
import { FrostedPill } from './FrostedPill';
import { NarrationText } from './NarrationText';
import { ProgressBar } from './ProgressBar';

export const defaultVeoSection03NarrationOverlayIntroProps = {};

export const VeoSection03NarrationOverlayIntro: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: 'transparent',
        justifyContent: 'flex-end',
        alignItems: 'center',
      }}
    >
      <FrostedPill>
        <NarrationText />
        <ProgressBar />
      </FrostedPill>
    </AbsoluteFill>
  );
};

export default VeoSection03NarrationOverlayIntro;
