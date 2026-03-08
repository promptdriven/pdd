import React from 'react';
import { AbsoluteFill } from 'remotion';
import { FrostedPill } from './FrostedPill';
import { AccentBar } from './AccentBar';
import { NarrationText } from './NarrationText';

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
        <AccentBar />
        <NarrationText />
      </FrostedPill>
    </AbsoluteFill>
  );
};

export default VeoSection05NarrationOverlayForest;
