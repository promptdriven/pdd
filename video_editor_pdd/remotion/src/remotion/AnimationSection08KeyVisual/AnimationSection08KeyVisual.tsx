import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, BARS, DIMENSIONS, TIMING, TYPOGRAPHY } from './constants';
import { AnimatedBar } from './AnimatedBar';

export const defaultAnimationSection08KeyVisualProps = {};

export const AnimationSection08KeyVisual: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      {/* Heading */}
      <div
        style={{
          position: 'absolute',
          top: TYPOGRAPHY.headingY,
          left: TYPOGRAPHY.headingX,
          color: COLORS.heading,
          fontSize: TYPOGRAPHY.headingSize,
          fontWeight: TYPOGRAPHY.headingWeight,
          fontFamily: TYPOGRAPHY.fontFamily,
        }}
      >
        Key Visual
      </div>

      {/* Bar chart container */}
      <div
        style={{
          display: 'flex',
          gap: DIMENSIONS.barGap,
          alignItems: 'flex-end',
          height: DIMENSIONS.containerHeight,
          position: 'relative',
        }}
      >
        {BARS.map((bar, index) => (
          <AnimatedBar
            key={index}
            targetHeight={bar.maxHeight}
            delay={index * TIMING.barStaggerDelay}
            color={bar.color}
          />
        ))}
      </div>
    </AbsoluteFill>
  );
};

export default AnimationSection08KeyVisual;
