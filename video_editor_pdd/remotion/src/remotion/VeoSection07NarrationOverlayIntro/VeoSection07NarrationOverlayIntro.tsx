import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { ANIMATION, NARRATION_TEXT } from './constants';
import { FrostedPill } from './FrostedPill';
import { ProgressBar } from './ProgressBar';

export const VeoSection07NarrationOverlayIntro: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 100-120: Entire overlay fades out with easeInQuad
  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  return (
    <AbsoluteFill
      style={{
        pointerEvents: 'none',
      }}
    >
      <AbsoluteFill style={{ opacity: fadeOutOpacity }}>
        <FrostedPill text={NARRATION_TEXT} />
        <ProgressBar />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export const defaultVeoSection07NarrationOverlayIntroProps = {};

export default VeoSection07NarrationOverlayIntro;
