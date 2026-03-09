import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, TYPOGRAPHY, POSITIONS, ANIMATION_TIMING } from './constants';
import { BorderTrace } from './BorderTrace';
import { ExpandingRule } from './ExpandingRule';
import { DiamondOrnament } from './DiamondOrnament';

export const VeoSection14SectionOutro: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fade-in from black to charcoal (frames 0-15)
  const bgOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.bgFadeStart, ANIMATION_TIMING.bgFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Title text fade-in and scale (frames 35-55)
  const titleOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.titleStart, ANIMATION_TIMING.titleEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  const titleScale = interpolate(
    frame,
    [ANIMATION_TIMING.titleStart, ANIMATION_TIMING.titleEnd],
    [0.95, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Final fade to black (frames 80-90)
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
        backgroundColor: COLORS.background,
        opacity: bgOpacity,
      }}
    >
      {/* Amber border frame tracing clockwise */}
      <BorderTrace />

      {/* Expanding horizontal rule */}
      <ExpandingRule />

      {/* Section title text */}
      <div
        style={{
          position: 'absolute',
          top: POSITIONS.titleCenterY - TYPOGRAPHY.title.fontSize / 2,
          left: 0,
          width: CANVAS.width,
          textAlign: 'center',
          opacity: titleOpacity,
          transform: `scale(${titleScale})`,
          fontFamily: TYPOGRAPHY.title.fontFamily,
          fontSize: TYPOGRAPHY.title.fontSize,
          fontWeight: TYPOGRAPHY.title.fontWeight,
          letterSpacing: TYPOGRAPHY.title.letterSpacing,
          textTransform: TYPOGRAPHY.title.textTransform,
          color: COLORS.titleText,
        }}
      >
        END OF VEO SECTION
      </div>

      {/* Diamond ornament below text */}
      <DiamondOrnament />

      {/* Fade to black overlay */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: CANVAS.width,
          height: CANVAS.height,
          backgroundColor: COLORS.black,
          opacity: fadeToBlack,
          pointerEvents: 'none',
        }}
      />
    </AbsoluteFill>
  );
};

export const defaultVeoSection14SectionOutroProps = {};

export default VeoSection14SectionOutro;
