import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TIMING, PULSE } from './constants';

export const GlowRing: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 2 (20-50): Fade in glow from 0 to 20% opacity
  const glowFadeOpacity = interpolate(
    frame,
    [TIMING.holdStart, TIMING.glowFadeEnd],
    [0, PULSE.glowOpacityRest],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Phase 3 (50-75): Pulse — expand diameter and peak opacity
  const pulseDiameterExpand = interpolate(
    frame,
    [TIMING.pulseStart, TIMING.pulseMid],
    [DIMENSIONS.glowDiameter, DIMENSIONS.glowExpandedDiameter],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );
  const pulseDiameterContract = interpolate(
    frame,
    [TIMING.pulseMid, TIMING.pulseEnd],
    [DIMENSIONS.glowExpandedDiameter, DIMENSIONS.glowDiameter],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  let diameter: number;
  if (frame < TIMING.pulseStart) {
    diameter = DIMENSIONS.glowDiameter;
  } else if (frame <= TIMING.pulseMid) {
    diameter = pulseDiameterExpand;
  } else if (frame <= TIMING.pulseEnd) {
    diameter = pulseDiameterContract;
  } else {
    diameter = DIMENSIONS.glowDiameter;
  }

  // Pulse opacity
  const pulseOpacityUp = interpolate(
    frame,
    [TIMING.pulseStart, TIMING.pulseMid],
    [PULSE.glowOpacityRest, PULSE.glowOpacityPeak],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const pulseOpacityDown = interpolate(
    frame,
    [TIMING.pulseMid, TIMING.pulseEnd],
    [PULSE.glowOpacityPeak, PULSE.glowOpacityRest],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Phase 4 (75-120): Gentle sinusoidal oscillation between 15%-25%
  const oscillationProgress = interpolate(
    frame,
    [TIMING.restStart, TIMING.totalDuration],
    [0, Math.PI * 2],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const oscillationOpacity =
    (PULSE.glowOpacityMin + PULSE.glowOpacityMax) / 2 +
    ((PULSE.glowOpacityMax - PULSE.glowOpacityMin) / 2) *
      Math.sin(oscillationProgress);

  // Compose final opacity across phases
  let opacity: number;
  if (frame < TIMING.holdStart) {
    opacity = 0;
  } else if (frame < TIMING.pulseStart) {
    opacity = glowFadeOpacity;
  } else if (frame <= TIMING.pulseMid) {
    opacity = pulseOpacityUp;
  } else if (frame <= TIMING.pulseEnd) {
    opacity = pulseOpacityDown;
  } else {
    opacity = oscillationOpacity;
  }

  return (
    <div
      style={{
        position: 'absolute',
        width: diameter,
        height: diameter,
        borderRadius: '50%',
        backgroundColor: COLORS.circle,
        opacity,
        filter: `blur(${DIMENSIONS.glowBlur}px)`,
        top: '50%',
        left: '50%',
        transform: 'translate(-50%, -50%)',
      }}
    />
  );
};
