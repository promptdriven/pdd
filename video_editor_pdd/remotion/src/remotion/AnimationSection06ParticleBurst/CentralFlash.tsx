import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, FLASH, TIMING } from './constants';

/**
 * Central radial glow that expands from 0→120px then contracts to 60px and fades.
 * Frames 0-3: expand (easeOutQuad), opacity 0→80%
 * Frames 3-6: contract and fade (easeInQuad), radius 120→60, opacity 80%→0
 */
export const CentralFlash: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame >= TIMING.flashFadeEnd) return null;

  // Phase 1: expand (frames 0-3)
  const expandRadius = interpolate(
    frame,
    [0, TIMING.flashExpandEnd],
    [0, FLASH.maxRadius],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const expandOpacity = interpolate(
    frame,
    [0, TIMING.flashExpandEnd],
    [0, FLASH.peakOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Phase 2: contract + fade (frames 3-6)
  const contractRadius = interpolate(
    frame,
    [TIMING.flashExpandEnd, TIMING.flashFadeEnd],
    [FLASH.maxRadius, FLASH.contractedRadius],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  const fadeOpacity = interpolate(
    frame,
    [TIMING.flashExpandEnd, TIMING.flashFadeEnd],
    [FLASH.peakOpacity, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  const radius = frame <= TIMING.flashExpandEnd ? expandRadius : contractRadius;
  const opacity = frame <= TIMING.flashExpandEnd ? expandOpacity : fadeOpacity;

  if (opacity <= 0) return null;

  const diameter = radius * 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.centerX - radius,
        top: CANVAS.centerY - radius,
        width: diameter,
        height: diameter,
        borderRadius: '50%',
        background: `radial-gradient(circle, ${COLORS.flash} 0%, transparent 70%)`,
        opacity,
      }}
    />
  );
};
