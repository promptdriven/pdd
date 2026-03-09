import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, TYPOGRAPHY, POSITIONS, ANIMATION } from './constants';

export const ArrowDivider: React.FC = () => {
  const frame = useCurrentFrame();

  // Gradient divider opacity (fades in with panels)
  const dividerOpacity = interpolate(
    frame,
    [ANIMATION.slideInStart, ANIMATION.slideInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Fade out with panels
  const dividerFadeOut = interpolate(
    frame,
    [ANIMATION.slideOutStart, ANIMATION.slideOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    }
  );

  // Arrow opacity: fade in frames 30-35
  const arrowOpacity = interpolate(
    frame,
    [ANIMATION.arrowFadeStart, ANIMATION.arrowFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Arrow pulse: scale 1.0 → 1.3 → 1.0 over frames 30-40
  const pulseMid = (ANIMATION.arrowPulseStart + ANIMATION.arrowPulseEnd) / 2;
  let arrowScale = 1.0;
  if (frame >= ANIMATION.arrowPulseStart && frame <= pulseMid) {
    arrowScale = interpolate(
      frame,
      [ANIMATION.arrowPulseStart, pulseMid],
      [1.0, 1.3],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      }
    );
  } else if (frame > pulseMid && frame <= ANIMATION.arrowPulseEnd) {
    arrowScale = interpolate(
      frame,
      [pulseMid, ANIMATION.arrowPulseEnd],
      [1.3, 1.0],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      }
    );
  }

  const combinedOpacity = dividerOpacity * dividerFadeOut;

  return (
    <>
      {/* Gradient divider zone */}
      <div
        style={{
          position: 'absolute',
          left: DIMENSIONS.dividerX,
          top: 0,
          width: DIMENSIONS.dividerWidth,
          height: CANVAS.height,
          background: `linear-gradient(to right, ${COLORS.dividerGradientStart}, transparent)`,
          opacity: combinedOpacity,
          zIndex: 10,
        }}
      />

      {/* Arrow icon */}
      <div
        style={{
          position: 'absolute',
          left: DIMENSIONS.dividerX,
          top: POSITIONS.arrowY,
          width: DIMENSIONS.dividerWidth,
          height: 48,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          opacity: arrowOpacity * dividerFadeOut,
          transform: `scale(${arrowScale})`,
          zIndex: 11,
        }}
      >
        <span
          style={{
            fontFamily: TYPOGRAPHY.arrow.fontFamily,
            fontSize: TYPOGRAPHY.arrow.fontSize,
            fontWeight: TYPOGRAPHY.arrow.fontWeight,
            color: COLORS.accent,
          }}
        >
          →
        </span>
      </div>
    </>
  );
};
