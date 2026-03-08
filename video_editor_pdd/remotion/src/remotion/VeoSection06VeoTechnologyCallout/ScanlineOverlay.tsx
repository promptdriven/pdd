import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION, CARD } from './constants';

export const ScanlineOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Scanline sweeps top to bottom repeatedly
  const scanPhase = (frame % ANIMATION.scanlinePeriod) / ANIMATION.scanlinePeriod;
  const scanY = interpolate(scanPhase, [0, 1], [-40, CARD.height + 40]);

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: CARD.width,
        height: CARD.height,
        borderRadius: CARD.borderRadius,
        overflow: 'hidden',
        pointerEvents: 'none',
      }}
    >
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: scanY,
          width: '100%',
          height: 40,
          background: `linear-gradient(180deg, transparent 0%, ${COLORS.scanline} 50%, transparent 100%)`,
        }}
      />
    </div>
  );
};
