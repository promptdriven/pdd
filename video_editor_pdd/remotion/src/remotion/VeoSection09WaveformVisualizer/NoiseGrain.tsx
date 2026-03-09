import React, { useMemo } from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS } from './constants';

/**
 * Subtle noise grain overlay rendered as an SVG filter.
 * 2% opacity per spec.
 */
export const NoiseGrain: React.FC = () => {
  const svgFilter = useMemo(
    () => (
      <svg width="0" height="0" style={{ position: 'absolute' }}>
        <filter id="waveform-noise">
          <feTurbulence
            type="fractalNoise"
            baseFrequency="0.65"
            numOctaves="3"
            stitchTiles="stitch"
          />
          <feColorMatrix type="saturate" values="0" />
        </filter>
      </svg>
    ),
    []
  );

  return (
    <>
      {svgFilter}
      <AbsoluteFill
        style={{
          width: CANVAS.width,
          height: CANVAS.height,
          filter: 'url(#waveform-noise)',
          opacity: 0.02,
          pointerEvents: 'none',
        }}
      />
    </>
  );
};
