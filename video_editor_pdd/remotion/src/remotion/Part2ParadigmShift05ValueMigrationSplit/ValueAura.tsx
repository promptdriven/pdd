import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  AURA_BLUR,
  AURA_PULSE_MIN,
  AURA_PULSE_MAX,
  AURA_PULSE_PERIOD,
  PHASE_4_START,
} from './constants';

interface ValueAuraProps {
  centerX: number;
  centerY: number;
  width: number;
  height: number;
  color: string;
  /** Frame at which the aura begins (default: PHASE_4_START = 160) */
  startFrame?: number;
}

/**
 * Pulsing glow aura effect rendered around a rectangular area.
 * Uses a blurred div to simulate a Gaussian glow.
 */
export const ValueAura: React.FC<ValueAuraProps> = ({
  centerX,
  centerY,
  width,
  height,
  color,
  startFrame = PHASE_4_START,
}) => {
  const frame = useCurrentFrame();

  // Fade in the aura over 30 frames
  const fadeIn = interpolate(
    frame,
    [startFrame, startFrame + 30],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Pulsing opacity using sine easing on a cycle
  const cycleFrame = (frame - startFrame) % AURA_PULSE_PERIOD;
  const pulseT = interpolate(
    cycleFrame,
    [0, AURA_PULSE_PERIOD / 2, AURA_PULSE_PERIOD],
    [0, 1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
  );
  const auraOpacity = fadeIn * interpolate(
    pulseT,
    [0, 1],
    [AURA_PULSE_MIN, AURA_PULSE_MAX],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  if (frame < startFrame) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: centerX - width / 2 - AURA_BLUR,
        top: centerY - height / 2 - AURA_BLUR,
        width: width + AURA_BLUR * 2,
        height: height + AURA_BLUR * 2,
        borderRadius: AURA_BLUR,
        backgroundColor: color,
        opacity: auraOpacity,
        filter: `blur(${AURA_BLUR}px)`,
        pointerEvents: 'none',
      }}
    />
  );
};

export default ValueAura;
