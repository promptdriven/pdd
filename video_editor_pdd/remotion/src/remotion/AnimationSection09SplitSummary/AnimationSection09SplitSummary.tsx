import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, DIVIDER, TIMING } from './constants';
import { SplitBackground } from './SplitBackground';
import { GlowingDivider } from './GlowingDivider';
import { SplitLabel } from './SplitLabel';

export const defaultAnimationSection09SplitSummaryProps = {};

export const AnimationSection09SplitSummary: React.FC = () => {
  const frame = useCurrentFrame();

  // Card fade-in: opacity 0→1 over frames 0-6, easeOutQuad
  const cardOpacity = interpolate(
    frame,
    [TIMING.fadeInStart, TIMING.fadeInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Divider X position (also needed for background split)
  const dividerX = interpolate(
    frame,
    [TIMING.driftStart, TIMING.driftEnd],
    [DIVIDER.startX, DIVIDER.endX],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.background,
        opacity: cardOpacity,
      }}
    >
      <SplitBackground dividerX={dividerX} />
      <GlowingDivider />
      <SplitLabel />
    </AbsoluteFill>
  );
};

export default AnimationSection09SplitSummary;
