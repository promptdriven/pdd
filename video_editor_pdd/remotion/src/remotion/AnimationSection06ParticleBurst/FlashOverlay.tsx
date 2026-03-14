import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, FLASH, TIMING } from './constants';

export const FlashOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 0-1: Ramp up to peak opacity (easeOutQuad)
  const rampUp = interpolate(
    frame,
    [TIMING.flashStart, 1],
    [0, FLASH.peakOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Frame 1-2: Fade back to 0 (easeInQuad)
  const fadeDown = interpolate(
    frame,
    [1, TIMING.flashEnd],
    [FLASH.peakOpacity, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  const opacity = frame <= 1 ? rampUp : fadeDown;

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
