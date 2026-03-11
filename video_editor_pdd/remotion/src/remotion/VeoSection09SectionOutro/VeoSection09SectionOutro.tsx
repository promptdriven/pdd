import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, TYPOGRAPHY, POSITIONS, ANIMATION_TIMING } from './constants';
import { BokehField } from './BokehField';
import { CheckmarkIcon } from './CheckmarkIcon';
import { FilmGrainOverlay } from './FilmGrainOverlay';

export const VeoSection09SectionOutro: React.FC = () => {
  const frame = useCurrentFrame();

  // Background crossfade in (frames 0-8)
  const crossfadeOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.crossfadeStart, ANIMATION_TIMING.crossfadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // "Section Complete" text fade-in with upward translate (frames 22-34)
  const textOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.textFadeStart, ANIMATION_TIMING.textFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  const textTranslateY = interpolate(
    frame,
    [ANIMATION_TIMING.textFadeStart, ANIMATION_TIMING.textFadeEnd],
    [15, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Fade to black (frames 34-42)
  const fadeToBlack = interpolate(
    frame,
    [ANIMATION_TIMING.fadeOutStart, ANIMATION_TIMING.fadeOutEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.gradientTop} 0%, ${COLORS.gradientBottom} 100%)`,
        opacity: crossfadeOpacity,
      }}
    >
      {/* Film grain overlay */}
      <FilmGrainOverlay />

      {/* Warm bokeh particles drifting diagonally */}
      <BokehField />

      {/* Animated checkmark icon */}
      <CheckmarkIcon />

      {/* "Section Complete" status text */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: POSITIONS.statusTextY,
          width: CANVAS.width,
          textAlign: 'center',
          opacity: textOpacity,
          transform: `translateY(${textTranslateY}px)`,
          fontFamily: TYPOGRAPHY.status.fontFamily,
          fontSize: TYPOGRAPHY.status.fontSize,
          fontWeight: TYPOGRAPHY.status.fontWeight,
          letterSpacing: TYPOGRAPHY.status.letterSpacing,
          textTransform: TYPOGRAPHY.status.textTransform,
          color: COLORS.statusText,
        }}
      >
        Section Complete
      </div>

      {/* Fade to black overlay */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: CANVAS.width,
          height: CANVAS.height,
          backgroundColor: '#00FF00',
          opacity: fadeToBlack,
          pointerEvents: 'none',
        }}
      />
    </AbsoluteFill>
  );
};

export const defaultVeoSection09SectionOutroProps = {};

export default VeoSection09SectionOutro;
