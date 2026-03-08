import React from 'react';
import { AbsoluteFill } from 'remotion';
import {
  COLORS,
  BARS,
  CHART,
  TYPOGRAPHY,
  POSITIONS,
  ANIMATION_TIMING,
} from './constants';
import { AnimatedBar } from './AnimatedBar';

export const AnimationSection05BarChartKeyVisual: React.FC = () => {
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
          top: POSITIONS.headingY,
          left: POSITIONS.headingX,
          fontSize: TYPOGRAPHY.heading.fontSize,
          fontFamily: TYPOGRAPHY.heading.fontFamily,
          fontWeight: TYPOGRAPHY.heading.fontWeight,
          color: COLORS.headingText,
        }}
      >
        Key Visual
      </div>

      {/* Bar chart container */}
      <div
        style={{
          position: 'absolute',
          top: CHART.baselineY - CHART.maxBarHeight - 40,
          display: 'flex',
          gap: CHART.gap,
          alignItems: 'flex-end',
          height: CHART.maxBarHeight + 40,
        }}
      >
        {BARS.map((bar, index) => (
          <AnimatedBar
            key={index}
            targetHeight={CHART.maxBarHeight * bar.value}
            delay={index * CHART.staggerDelayFrames}
            color={bar.color}
            label={`${Math.round(bar.value * 100)}%`}
            labelDelay={
              ANIMATION_TIMING.labelFadeStart +
              index * ANIMATION_TIMING.labelStagger
            }
          />
        ))}
      </div>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection05BarChartKeyVisualProps = {};

export default AnimationSection05BarChartKeyVisual;
