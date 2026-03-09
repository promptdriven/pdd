import React from 'react';
import { AbsoluteFill } from 'remotion';
import { FrostedPill } from './FrostedPill';
import { NarrationText } from './NarrationText';
import { ProgressBar } from './ProgressBar';

export const defaultVeoSection05NarrationOverlayForestProps = {};

export const VeoSection05NarrationOverlayForest: React.FC = () => {
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

export default VeoSection05NarrationOverlayForest;
