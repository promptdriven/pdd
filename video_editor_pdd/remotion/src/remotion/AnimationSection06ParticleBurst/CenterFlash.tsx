import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, FLASH, TIMING } from './constants';

export const CenterFlash: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 0-2: scale from 0 to full diameter, easeOutQuad
  const scale = interpolate(
    frame,
    [TIMING.flashScaleStart, TIMING.flashScaleEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Frame 0-2: opacity at peak; Frame 2-3: fade to 0, easeInQuad
  const opacity =
    frame <= TIMING.flashFadeStart
      ? FLASH.peakOpacity
      : interpolate(
          frame,
          [TIMING.flashFadeStart, TIMING.flashFadeEnd],
          [FLASH.peakOpacity, 0],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.in(Easing.quad),
          }
        );

  if (frame > TIMING.flashFadeEnd + 1) return null;

  const diameter = FLASH.diameter * scale;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.centerX - diameter / 2,
        top: CANVAS.centerY - diameter / 2,
        width: diameter,
        height: diameter,
        borderRadius: '50%',
        backgroundColor: COLORS.flash,
        opacity,
        boxShadow: `0 0 ${diameter}px ${diameter / 2}px rgba(255,255,255,${opacity * 0.4})`,
      }}
    />
  );
};
