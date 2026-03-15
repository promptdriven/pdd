import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, BARS, DIMENSIONS, TIMING, TYPOGRAPHY } from './constants';
import { AnimatedBar } from './AnimatedBar';
import { GridLines } from './GridLines';

export const defaultAnimationSection08KeyVisualProps = {};

export const AnimationSection08KeyVisual: React.FC = () => {
  const frame = useCurrentFrame();

  // Label fade-in: frames 0–4, easeOutQuad
  const labelOpacity = interpolate(
    frame,
    [TIMING.labelFadeStart, TIMING.labelFadeEnd],
    [0, TYPOGRAPHY.labelOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Total container width = 4 bars * 120px + 3 gaps * 30px = 570px
  // Center within the 600px logical container
  const totalBarsWidth =
    BARS.length * DIMENSIONS.barWidth +
    (BARS.length - 1) * DIMENSIONS.barGap;
  const containerLeft =
    (DIMENSIONS.canvasWidth - totalBarsWidth) / 2;

  const tallestHeight = Math.max(...BARS.map((b) => b.height));

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Grid lines */}
      <GridLines />

      {/* "Key Visual" label */}
      <div
        style={{
          position: 'absolute',
          top: TYPOGRAPHY.labelY,
          left: TYPOGRAPHY.labelX,
          color: COLORS.white,
          fontSize: TYPOGRAPHY.labelSize,
          fontWeight: TYPOGRAPHY.labelWeight,
          fontFamily: TYPOGRAPHY.fontFamily,
          opacity: labelOpacity,
        }}
      >
        Key Visual
      </div>

      {/* Bar chart container — bottom-anchored at y=880 */}
      <div
        style={{
          position: 'absolute',
          left: containerLeft,
          bottom: DIMENSIONS.canvasHeight - DIMENSIONS.containerBottomY,
          display: 'flex',
          gap: DIMENSIONS.barGap,
          alignItems: 'flex-end',
          height: DIMENSIONS.maxHeight,
        }}
      >
        {BARS.map((bar, index) => (
          <AnimatedBar
            key={index}
            targetHeight={bar.height}
            delay={2 + index * TIMING.barStaggerFrames}
            color={bar.color}
            isTallest={bar.height === tallestHeight}
          />
        ))}
      </div>
    </AbsoluteFill>
  );
};

export default AnimationSection08KeyVisual;
