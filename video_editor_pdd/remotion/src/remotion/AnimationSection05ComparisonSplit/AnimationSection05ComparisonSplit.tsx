import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, useVideoConfig, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TIMING, TYPOGRAPHY } from './constants';
import { Panel } from './Panel';
import { SlidingDivider } from './SlidingDivider';

export const defaultAnimationSection05ComparisonSplitProps = {};

export const AnimationSection05ComparisonSplit: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Panel fade in (0-0.67s, frames 0-20)
  const panelOpacity = interpolate(
    frame,
    [0, 20],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.ease),
    }
  );

  // Divider slide animation (1.0-3.0s, frames 30-90)
  const dividerX = interpolate(
    frame,
    [30, 90],
    [DIMENSIONS.splitPosition, DIMENSIONS.canvasWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Divider bounce (3.0-4.0s, frames 90-120)
  const bounceX = interpolate(
    frame,
    [90, 105, 120],
    [0, -40, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.5)),
    }
  );

  const finalDividerX = frame >= 90 ? dividerX + bounceX : dividerX;

  // Glow pulse on "After" side (4.0-5.0s, frames 120-150)
  const glowIntensity = interpolate(
    frame,
    [120, 135, 150],
    [0.3, 0.6, 0.3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  // Reveal mask for After panel
  const revealX = interpolate(
    frame,
    [30, 90],
    [DIMENSIONS.splitPosition, DIMENSIONS.canvasWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Before Panel (Left) */}
      <div style={{ opacity: panelOpacity }}>
        <Panel
          side="left"
          label="Before"
          labelColor={COLORS.beforeText}
          backgroundColor={COLORS.beforeBg}
          labelBgColor={COLORS.beforeLabelBg}
        />
      </div>

      {/* After Panel (Right) with reveal mask */}
      <div
        style={{
          opacity: panelOpacity,
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          clipPath: `inset(0 0 0 ${revealX}px)`,
        }}
      >
        <Panel
          side="right"
          label="After"
          labelColor={COLORS.afterText}
          backgroundColor={COLORS.afterBg}
          labelBgColor={COLORS.afterLabelBg}
          glowIntensity={frame >= 120 ? glowIntensity : 0}
        />
      </div>

      {/* Sliding Divider */}
      {frame >= 30 && (
        <SlidingDivider
          x={finalDividerX}
          color={COLORS.divider}
          width={DIMENSIONS.dividerWidth}
          height={DIMENSIONS.canvasHeight}
        />
      )}
    </AbsoluteFill>
  );
};

export default AnimationSection05ComparisonSplit;
