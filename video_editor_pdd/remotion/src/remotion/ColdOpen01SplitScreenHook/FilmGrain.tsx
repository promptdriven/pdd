import React, { useMemo } from 'react';
import { useCurrentFrame } from 'remotion';
import { FILM_GRAIN_FPS, FILM_GRAIN_OPACITY } from './constants';

/**
 * Animated monochrome film grain overlay.
 * Re-seeds at FILM_GRAIN_FPS to mimic analog noise cadence.
 */
export const FilmGrain: React.FC<{
  width: number;
  height: number;
  opacity?: number;
  fps?: number;
}> = ({ width, height, opacity = FILM_GRAIN_OPACITY, fps = FILM_GRAIN_FPS }) => {
  const frame = useCurrentFrame();

  // Only change the grain pattern at the specified fps
  const grainFrame = Math.floor(frame / (30 / fps));

  const grainStyle = useMemo(() => {
    // Generate a pseudo-random SVG noise pattern keyed to grainFrame
    const seed = grainFrame;
    return {
      position: 'absolute' as const,
      top: 0,
      left: 0,
      width,
      height,
      opacity,
      pointerEvents: 'none' as const,
      mixBlendMode: 'overlay' as const,
      zIndex: 3,
    };
  }, [grainFrame, width, height, opacity]);

  // Use SVG feTurbulence for performant noise
  const filterId = `grain-${grainFrame}`;

  return (
    <div style={grainStyle}>
      <svg width={width} height={height} style={{ display: 'block' }}>
        <filter id={filterId}>
          <feTurbulence
            type="fractalNoise"
            baseFrequency="0.65"
            numOctaves={3}
            seed={grainFrame}
            stitchTiles="stitch"
          />
          <feColorMatrix type="saturate" values="0" />
        </filter>
        <rect
          width={width}
          height={height}
          filter={`url(#${filterId})`}
          opacity={1}
        />
      </svg>
    </div>
  );
};

export default FilmGrain;
