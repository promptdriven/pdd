import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TIMING, PULSE } from './constants';

export const GlowRing: React.FC = () => {
  const frame = useCurrentFrame();

  // Glow fades in during settle phase (frames 8-15)
  const glowFadeIn = interpolate(
    frame,
    [TIMING.settleStart, TIMING.settleEnd],
    [0, PULSE.glowOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulse phase (frames 15-28): glow expands 220→280→220
  const pulseDiameterExpand = interpolate(
    frame,
    [TIMING.pulseStart, TIMING.pulsePeak],
    [DIMENSIONS.glowMinDiameter, DIMENSIONS.glowMaxDiameter],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );
  const pulseDiameterContract = interpolate(
    frame,
    [TIMING.pulsePeak, TIMING.pulseEnd],
    [DIMENSIONS.glowMaxDiameter, DIMENSIONS.glowMinDiameter],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Breathing phase (frames 28-45): sinusoidal opacity 0.12–0.18
  const breathingProgress = interpolate(
    frame,
    [TIMING.breathingStart, TIMING.breathingEnd],
    [0, Math.PI * 2],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Determine current diameter
  let diameter: number;
  if (frame < TIMING.pulseStart) {
    diameter = DIMENSIONS.glowMinDiameter;
  } else if (frame <= TIMING.pulsePeak) {
    diameter = pulseDiameterExpand;
  } else if (frame <= TIMING.pulseEnd) {
    diameter = pulseDiameterContract;
  } else {
    diameter = DIMENSIONS.glowMinDiameter;
  }

  // Determine current opacity
  let opacity: number;
  if (frame < TIMING.settleStart) {
    opacity = 0;
  } else if (frame < TIMING.breathingStart) {
    opacity = glowFadeIn;
  } else {
    const mid = (PULSE.breathingOpacityMin + PULSE.breathingOpacityMax) / 2;
    const amp = (PULSE.breathingOpacityMax - PULSE.breathingOpacityMin) / 2;
    opacity = mid + amp * Math.sin(breathingProgress);
  }

  // Circular glow halo behind the triangle for visual consistency
  return (
    <div
      style={{
        position: 'absolute',
        width: diameter,
        height: diameter,
        borderRadius: '50%',
        backgroundColor: COLORS.triangle,
        opacity,
        filter: `blur(${DIMENSIONS.glowBlur}px)`,
        top: '50%',
        left: '50%',
        transform: 'translate(-50%, -50%)',
      }}
    />
  );
};
