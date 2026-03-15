import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, CIRCLE, TIMING, GLOW_OPACITY } from './constants';

export const GlowEffect: React.FC = () => {
  const frame = useCurrentFrame();

  // Glow radius tracks circle radius + 20px offset
  let glowRadius: number;
  let glowOpacity: number;

  if (frame <= TIMING.fadeInEnd) {
    // Phase 1 (frames 0-5): Glow fades in with circle
    const fadeProgress = interpolate(
      frame,
      [TIMING.fadeInStart, TIMING.fadeInEnd],
      [0, 1],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
    );
    glowRadius = CIRCLE.baseRadius + CIRCLE.glowOffsetRadius;
    glowOpacity = GLOW_OPACITY.afterFadeIn * fadeProgress;
  } else if (frame <= TIMING.pulse1ExpandEnd) {
    // Phase 2 (frames 5-12): Glow brightens to 40%, radius expands
    glowOpacity = interpolate(
      frame,
      [TIMING.pulse1ExpandStart, TIMING.pulse1ExpandEnd],
      [GLOW_OPACITY.afterFadeIn, GLOW_OPACITY.pulse1Peak],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
    glowRadius = interpolate(
      frame,
      [TIMING.pulse1ExpandStart, TIMING.pulse1ExpandEnd],
      [CIRCLE.baseRadius + CIRCLE.glowOffsetRadius, CIRCLE.pulse1Radius + CIRCLE.glowOffsetRadius],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.sin) }
    );
  } else if (frame <= TIMING.pulse1ContractEnd) {
    // Phase 3 (frames 12-18): Glow fades to 15%, radius contracts
    glowOpacity = interpolate(
      frame,
      [TIMING.pulse1ContractStart, TIMING.pulse1ContractEnd],
      [GLOW_OPACITY.pulse1Peak, GLOW_OPACITY.afterPulse1],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
    glowRadius = interpolate(
      frame,
      [TIMING.pulse1ContractStart, TIMING.pulse1ContractEnd],
      [CIRCLE.pulse1Radius + CIRCLE.glowOffsetRadius, CIRCLE.baseRadius + CIRCLE.glowOffsetRadius],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.sin) }
    );
  } else if (frame <= TIMING.pulse2ExpandEnd) {
    // Phase 4 (frames 18-24): Second pulse glow brightens to 35%, radius expands
    glowOpacity = interpolate(
      frame,
      [TIMING.pulse2ExpandStart, TIMING.pulse2ExpandEnd],
      [GLOW_OPACITY.afterPulse1, GLOW_OPACITY.pulse2Peak],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
    glowRadius = interpolate(
      frame,
      [TIMING.pulse2ExpandStart, TIMING.pulse2ExpandEnd],
      [CIRCLE.baseRadius + CIRCLE.glowOffsetRadius, CIRCLE.pulse2Radius + CIRCLE.glowOffsetRadius],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.sin) }
    );
  } else {
    // Phase 5 (frames 24-30): Glow settles at 20%, radius contracts
    glowOpacity = interpolate(
      frame,
      [TIMING.pulse2ContractStart, TIMING.pulse2ContractEnd],
      [GLOW_OPACITY.pulse2Peak, GLOW_OPACITY.final],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
    glowRadius = interpolate(
      frame,
      [TIMING.pulse2ContractStart, TIMING.pulse2ContractEnd],
      [CIRCLE.pulse2Radius + CIRCLE.glowOffsetRadius, CIRCLE.baseRadius + CIRCLE.glowOffsetRadius],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.sin) }
    );
  }

  const glowDiameter = glowRadius * 2;

  return (
    <div
      style={{
        position: 'absolute',
        width: glowDiameter,
        height: glowDiameter,
        borderRadius: '50%',
        backgroundColor: COLORS.circleFill,
        opacity: glowOpacity,
        filter: `blur(${CIRCLE.glowBlur}px)`,
        top: CANVAS.centerY - glowRadius,
        left: CANVAS.centerX - glowRadius,
        pointerEvents: 'none',
      }}
    />
  );
};
