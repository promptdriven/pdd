import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, ANIMATION_TIMING } from './constants';
import { VerticalDivider } from './VerticalDivider';
import { AnimatedCircle } from './AnimatedCircle';
import { AnimatedSquare } from './AnimatedSquare';
import { FadeInLabel } from './FadeInLabel';

export const AnimationSection05SplitComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel backgrounds tint in during divider draw phase
  const panelOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.dividerDrawStart, ANIMATION_TIMING.dividerDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: '#0A1628',
      }}
    >
      {/* Left panel background */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: CANVAS.width / 2,
          height: CANVAS.height,
          backgroundColor: COLORS.leftPanelBg,
          opacity: panelOpacity,
        }}
      />

      {/* Right panel background */}
      <div
        style={{
          position: 'absolute',
          left: CANVAS.width / 2,
          top: 0,
          width: CANVAS.width / 2,
          height: CANVAS.height,
          backgroundColor: COLORS.rightPanelBg,
          opacity: panelOpacity,
        }}
      />

      {/* Vertical divider line */}
      <VerticalDivider />

      {/* Blue circle on left */}
      <AnimatedCircle />

      {/* Green square on right */}
      <AnimatedSquare />

      {/* Labels */}
      <FadeInLabel text="Circle" x={320} />
      <FadeInLabel text="Square" x={960} />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection05SplitComparisonProps = {};

export default AnimationSection05SplitComparison;
