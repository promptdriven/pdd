import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  AURA_APPEAR_START,
  AURA_APPEAR_END,
  AURA_INTENSIFY_START,
  AURA_INTENSIFY_END,
  AURA_MAX_OPACITY,
} from './constants';

interface AuraGlowProps {
  color: string;
  intenseColor: string;
  intenseOpacity: number;
  /**
   * Vertical position of the aura center as a fraction (0 = top, 1 = bottom).
   * Default 0.5 (center).
   */
  centerY?: number;
  /**
   * Horizontal position of the aura center as a fraction (0 = left, 1 = right).
   * Default 0.5 (center).
   */
  centerX?: number;
}

const AuraGlow: React.FC<AuraGlowProps> = ({
  color,
  intenseColor,
  intenseOpacity,
  centerY = 0.5,
  centerX = 0.5,
}) => {
  const frame = useCurrentFrame();

  // Phase 1: Aura appears (120–240), opacity goes from 0 → AURA_MAX_OPACITY
  const appearOpacity = interpolate(
    frame,
    [AURA_APPEAR_START, AURA_APPEAR_END],
    [0, AURA_MAX_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.ease),
    },
  );

  // Phase 2: Aura intensifies (240–360), opacity goes from AURA_MAX_OPACITY → intenseOpacity
  const intensifyOpacity = interpolate(
    frame,
    [AURA_INTENSIFY_START, AURA_INTENSIFY_END],
    [AURA_MAX_OPACITY, intenseOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  // Blend current color between base and intense
  const intensifyT = interpolate(
    frame,
    [AURA_INTENSIFY_START, AURA_INTENSIFY_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const opacity = frame < AURA_INTENSIFY_START ? appearOpacity : intensifyOpacity;

  // Scale increases slightly during intensify (two separate interpolations to avoid
  // non-strictly-increasing inputRange when AURA_APPEAR_END === AURA_INTENSIFY_START)
  const scaleAppear = interpolate(
    frame,
    [AURA_APPEAR_START, AURA_APPEAR_END],
    [0.6, 1.0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );
  const scaleIntensify = interpolate(
    frame,
    [AURA_INTENSIFY_START, AURA_INTENSIFY_END],
    [1.0, 1.2],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );
  const scale = frame < AURA_INTENSIFY_START ? scaleAppear : scaleIntensify;

  if (frame < AURA_APPEAR_START) return null;

  // Blend from color to intenseColor
  const currentColor = intensifyT > 0 ? intenseColor : color;

  const cx = `${centerX * 100}%`;
  const cy = `${centerY * 100}%`;

  return (
    <AbsoluteFill
      style={{
        pointerEvents: 'none',
      }}
    >
      {/* Primary radial glow */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          background: `radial-gradient(ellipse ${60 * scale}% ${55 * scale}% at ${cx} ${cy}, ${currentColor} 0%, transparent 100%)`,
          opacity,
          mixBlendMode: 'screen',
        }}
      />
      {/* Inner bright core */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          background: `radial-gradient(ellipse ${30 * scale}% ${25 * scale}% at ${cx} ${cy}, ${currentColor} 0%, transparent 100%)`,
          opacity: opacity * 0.5,
          mixBlendMode: 'screen',
        }}
      />
    </AbsoluteFill>
  );
};

export default AuraGlow;
