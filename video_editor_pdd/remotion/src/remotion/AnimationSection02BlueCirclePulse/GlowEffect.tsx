import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, CIRCLE, TIMING } from './constants';

export const GlowEffect: React.FC = () => {
  const frame = useCurrentFrame();

  const baseGlowOpacity = 0.2;
  const restGlowRadius = CIRCLE.baseRadius + 20; // 80px at rest

  let glowOpacity: number;
  let glowRadius: number;

  if (frame < TIMING.pulse1Start) {
    // Phase 1 (frames 0-5): Glow fades in during circle appear
    glowOpacity = interpolate(
      frame,
      [TIMING.appearStart, TIMING.appearEnd],
      [0, baseGlowOpacity * 0.3],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
    );
    glowRadius = restGlowRadius;
  } else if (frame < TIMING.contract1Start) {
    // Phase 2 (frames 5-15): Glow expands from 80px to 120px with pulse
    glowOpacity = interpolate(
      frame,
      [TIMING.pulse1Start, TIMING.pulse1End],
      [baseGlowOpacity * 0.3, baseGlowOpacity],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
    glowRadius = interpolate(
      frame,
      [TIMING.pulse1Start, TIMING.pulse1End],
      [restGlowRadius, CIRCLE.glowRadius],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
  } else if (frame < TIMING.pulse2Start) {
    // Phase 3 (frames 15-20): Glow contracts and fades
    glowOpacity = interpolate(
      frame,
      [TIMING.contract1Start, TIMING.contract1End],
      [baseGlowOpacity, baseGlowOpacity * 0.3],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
    glowRadius = interpolate(
      frame,
      [TIMING.contract1Start, TIMING.contract1End],
      [CIRCLE.glowRadius, restGlowRadius],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
  } else if (frame < TIMING.holdStart) {
    // Phase 4 (frames 20-28): Second pulse glow — expand then contract
    const mid = (TIMING.pulse2Start + TIMING.pulse2End) / 2;
    if (frame <= mid) {
      glowOpacity = interpolate(
        frame,
        [TIMING.pulse2Start, mid],
        [baseGlowOpacity * 0.3, baseGlowOpacity],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
      );
      glowRadius = interpolate(
        frame,
        [TIMING.pulse2Start, mid],
        [restGlowRadius, CIRCLE.glowRadius],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
      );
    } else {
      glowOpacity = interpolate(
        frame,
        [mid, TIMING.pulse2End],
        [baseGlowOpacity, baseGlowOpacity * 0.3],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
      );
      glowRadius = interpolate(
        frame,
        [mid, TIMING.pulse2End],
        [CIRCLE.glowRadius, restGlowRadius],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
      );
    }
  } else {
    // Phase 5 (frames 28-30): Hold at rest
    glowOpacity = baseGlowOpacity * 0.3;
    glowRadius = restGlowRadius;
  }

  const glowDiameter = glowRadius * 2;

  return (
    <div
      style={{
        position: 'absolute',
        width: glowDiameter,
        height: glowDiameter,
        borderRadius: '50%',
        background: `radial-gradient(circle, ${COLORS.circleFill} 0%, transparent 70%)`,
        opacity: glowOpacity,
        top: CANVAS.centerY - glowRadius,
        left: CANVAS.centerX - glowRadius,
        pointerEvents: 'none',
      }}
    />
  );
};
