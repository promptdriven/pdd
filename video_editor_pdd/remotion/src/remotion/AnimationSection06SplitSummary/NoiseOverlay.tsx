import React, { useMemo } from 'react';

/**
 * Renders a faint static noise texture using an SVG filter.
 * Purely decorative — gives the "Before" panel a raw/static look.
 */
export const NoiseOverlay: React.FC<{ opacity: number }> = ({ opacity }) => {
  const filterId = useMemo(() => 'noise-filter-split-summary', []);

  return (
    <div
      style={{
        position: 'absolute',
        inset: 0,
        opacity,
        pointerEvents: 'none',
      }}
    >
      <svg width="100%" height="100%" style={{ position: 'absolute', inset: 0 }}>
        <defs>
          <filter id={filterId}>
            <feTurbulence
              type="fractalNoise"
              baseFrequency="0.9"
              numOctaves={4}
              seed={42}
              stitchTiles="stitch"
            />
            <feColorMatrix type="saturate" values="0" />
          </filter>
        </defs>
        <rect width="100%" height="100%" filter={`url(#${filterId})`} />
      </svg>
    </div>
  );
};
