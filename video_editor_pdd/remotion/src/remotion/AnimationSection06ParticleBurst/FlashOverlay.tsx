import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, FLASH, TIMING } from './constants';

export const FlashOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Flash appears at frame 0 at peak opacity, fades out by frame 2
  const opacity = interpolate(
    frame,
    [TIMING.flashStart, TIMING.flashEnd],
    [FLASH.peakOpacity, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.exp),
    }
  );

  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        backgroundColor: COLORS.flash,
        opacity,
      }}
    />
  );
};
