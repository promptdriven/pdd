import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION_TIMING } from './constants';
import { GradientBar } from './GradientBar';
import { AccentLine } from './AccentLine';
import { TypeOnText } from './TypeOnText';

export const defaultVeoSection03NarrationOverlayIntroProps = {};

export const VeoSection03NarrationOverlayIntro: React.FC = () => {
  const frame = useCurrentFrame();

  // Global fade-out for all elements
  const fadeOut = interpolate(
    frame,
    [ANIMATION_TIMING.fadeOutStart, ANIMATION_TIMING.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        justifyContent: 'flex-end',
      }}
    >
      <AbsoluteFill style={{ opacity: fadeOut }}>
        <GradientBar />
        <AccentLine />
        <TypeOnText />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default VeoSection03NarrationOverlayIntro;
