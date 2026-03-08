import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, BARS, DIMENSIONS, TIMING, TYPOGRAPHY } from './constants';
import { AnimatedBar } from './AnimatedBar';

export const defaultAnimationSection02BarChartKeyVisualProps = {};

export const AnimationSection02BarChartKeyVisual: React.FC = () => {
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
          height: DIMENSIONS.maxBarHeight + 40,
          position: 'absolute',
          top: DIMENSIONS.baseline - DIMENSIONS.maxBarHeight - 40,
          left: '50%',
          transform: 'translateX(-50%)',
        }}
      >
        {BARS.map((bar, index) => (
          <AnimatedBar
            key={index}
            targetHeight={DIMENSIONS.maxBarHeight * bar.value}
            delay={index * TIMING.barStaggerDelay}
            color={bar.color}
            label={bar.percentLabel}
            labelDelay={TIMING.labelFadeStart + index * TIMING.labelStaggerDelay}
          />
        ))}
      </div>
    </AbsoluteFill>
  );
};

export default AnimationSection02BarChartKeyVisual;
