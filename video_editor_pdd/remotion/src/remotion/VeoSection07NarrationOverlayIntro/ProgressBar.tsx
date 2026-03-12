import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION, type NarrationOverlayLayout } from './constants';

export const ProgressBar: React.FC<{ layout: NarrationOverlayLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  // Frame 0-120: Progress bar fills linearly
  const widthPercent = interpolate(
    frame,
    [ANIMATION.progressStart, ANIMATION.progressEnd],
    [0, 100],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: layout.pill.x,
        top: layout.pill.y + layout.pill.height + layout.dimensions.progressBarGap,
        width: layout.pill.width,
        height: layout.dimensions.progressBarHeight,
        backgroundColor: 'rgba(91,155,213,0.15)',
        borderRadius: layout.dimensions.progressBarHeight / 2,
        overflow: 'hidden',
      }}
    >
      <div
        style={{
          width: `${widthPercent}%`,
          height: '100%',
          backgroundColor: COLORS.progressBar,
          opacity: layout.dimensions.progressBarOpacity,
          borderRadius: layout.dimensions.progressBarHeight / 2,
        }}
      />
    </div>
  );
};
