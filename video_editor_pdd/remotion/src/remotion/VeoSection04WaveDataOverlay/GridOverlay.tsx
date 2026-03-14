import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, GRID, type WaveOverlayLayout } from './constants';

interface GridOverlayProps {
  layout: WaveOverlayLayout;
}

export const GridOverlay: React.FC<GridOverlayProps> = ({ layout }) => {
  const frame = useCurrentFrame();

  // Grid lines fade in with the overlay (frame 0–8), easeOutQuad
  const opacity = interpolate(
    frame,
    [ANIMATION.overlayFadeStart, ANIMATION.overlayFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <svg
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: layout.width,
        height: layout.height,
        opacity,
        pointerEvents: 'none',
      }}
    >
      {GRID.intervals.map((fraction) => {
        const y = layout.height * fraction;
        return (
          <line
            key={fraction}
            x1={0}
            y1={y}
            x2={layout.width}
            y2={y}
            stroke={COLORS.gridLine}
            strokeWidth={1}
          />
        );
      })}
    </svg>
  );
};
