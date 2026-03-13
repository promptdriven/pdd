import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, CIRCLE, TIMING } from './constants';

export const GlowEffect: React.FC = () => {
  const frame = useCurrentFrame();

  // Glow appears after the initial scale-in
  const baseGlowOpacity = 0.2;

  // Phase 1: No glow during appear
  // Phase 2 (pulse 1): Glow expands from 80 to 120 and is visible
  // Phase 3 (contract 1): Glow fades
  // Phase 4 (pulse 2): Glow reappears
  // Phase 5 (hold): Glow at rest

  let glowOpacity: number;
  let glowRadius: number;

  if (frame < TIMING.pulse1Start) {
    // Fade in glow during appear
    glowOpacity = interpolate(frame, [TIMING.appearStart, TIMING.appearEnd], [0, baseGlowOpacity * 0.5], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    });
    glowRadius = CIRCLE.baseRadius + 20;
  } else if (frame < TIMING.contract1Start) {
    // Pulse 1: glow expands and brightens
    const mid = (TIMING.pulse1Start + TIMING.pulse1End) / 2;
    if (frame <= mid) {
      glowOpacity = interpolate(frame, [TIMING.pulse1Start, mid], [baseGlowOpacity * 0.5, baseGlowOpacity], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      });
      glowRadius = interpolate(frame, [TIMING.pulse1Start, mid], [CIRCLE.baseRadius + 20, CIRCLE.glowRadius], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      });
    } else {
      glowOpacity = interpolate(frame, [mid, TIMING.pulse1End], [baseGlowOpacity, baseGlowOpacity * 0.7], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      });
      glowRadius = interpolate(frame, [mid, TIMING.pulse1End], [CIRCLE.glowRadius, CIRCLE.baseRadius + 30], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      });
    }
  } else if (frame < TIMING.pulse2Start) {
    // Contract: glow fades
    glowOpacity = interpolate(frame, [TIMING.contract1Start, TIMING.contract1End], [baseGlowOpacity * 0.7, baseGlowOpacity * 0.3], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    });
    glowRadius = interpolate(frame, [TIMING.contract1Start, TIMING.contract1End], [CIRCLE.baseRadius + 30, CIRCLE.baseRadius + 20], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    });
  } else if (frame < TIMING.holdStart) {
    // Pulse 2: same expansion pattern
    const mid = (TIMING.pulse2Start + TIMING.pulse2End) / 2;
    if (frame <= mid) {
      glowOpacity = interpolate(frame, [TIMING.pulse2Start, mid], [baseGlowOpacity * 0.3, baseGlowOpacity], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      });
      glowRadius = interpolate(frame, [TIMING.pulse2Start, mid], [CIRCLE.baseRadius + 20, CIRCLE.glowRadius], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      });
    } else {
      glowOpacity = interpolate(frame, [mid, TIMING.pulse2End], [baseGlowOpacity, baseGlowOpacity * 0.5], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      });
      glowRadius = interpolate(frame, [mid, TIMING.pulse2End], [CIRCLE.glowRadius, CIRCLE.baseRadius + 20], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      });
    }
  } else {
    // Hold
    glowOpacity = baseGlowOpacity * 0.5;
    glowRadius = CIRCLE.baseRadius + 20;
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
