import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { ANIMATION } from './constants';
import { GradientBar } from './GradientBar';
import { BadgePill } from './BadgePill';
import { TypeOnSubtitle } from './TypeOnSubtitle';
import { ProgressBar } from './ProgressBar';

export const VeoSection06VeoBadgeCallout: React.FC = () => {
  const frame = useCurrentFrame();

  // Global fade out: frames 80-90, easeInCubic
  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(3)),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: 'transparent',
        opacity: fadeOutOpacity,
      }}
    >
      {/* Bottom gradient bar */}
      <GradientBar />

      {/* "VEO GENERATED" pill badge */}
      <BadgePill />

      {/* Typewriter subtitle text */}
      <TypeOnSubtitle />

      {/* Bottom progress bar */}
      <ProgressBar />
    </AbsoluteFill>
  );
};

export const defaultVeoSection06VeoBadgeCalloutProps = {};

export default VeoSection06VeoBadgeCallout;
