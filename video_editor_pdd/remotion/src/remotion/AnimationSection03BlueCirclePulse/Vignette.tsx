import React from 'react';
import { AbsoluteFill } from 'remotion';

export const Vignette: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        background:
          'radial-gradient(ellipse at center, transparent 40%, rgba(0,0,0,0.3) 100%)',
      }}
    />
  );
};
