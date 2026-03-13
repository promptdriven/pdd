import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, interpolateColors, Easing } from 'remotion';
import { CANVAS, COLORS, ANIMATION_TIMING } from './constants';
import { VerticalDivider } from './VerticalDivider';
import { AnimatedCircle } from './AnimatedCircle';
import { AnimatedSquare } from './AnimatedSquare';
import { FadeInLabel } from './FadeInLabel';

export const AnimationSection05SplitComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel backgrounds tint in from base color to their respective colors
  const leftBg = interpolateColors(
    frame,
    [ANIMATION_TIMING.dividerDrawStart, ANIMATION_TIMING.dividerDrawEnd],
    [COLORS.baseBg, COLORS.leftPanelBg]
  );

  const rightBg = interpolateColors(
    frame,
    [ANIMATION_TIMING.dividerDrawStart, ANIMATION_TIMING.dividerDrawEnd],
    [COLORS.baseBg, COLORS.rightPanelBg]
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.baseBg,
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
          backgroundColor: leftBg,
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
          backgroundColor: rightBg,
        }}
      />

      {/* Vertical divider line */}
      <VerticalDivider />

      {/* Blue circle on left */}
      <AnimatedCircle />

      {/* Green square on right */}
      <AnimatedSquare />

      {/* Labels with staggered fade-in */}
      <FadeInLabel text="Circle" x={320} fadeStart={ANIMATION_TIMING.circleLabelFadeStart} />
      <FadeInLabel text="Square" x={960} fadeStart={ANIMATION_TIMING.squareLabelFadeStart} />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection05SplitComparisonProps = {};

export default AnimationSection05SplitComparison;
