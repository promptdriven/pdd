/**
 * AnimationSection03CircularProgressIndicators
 *
 * Three circular progress indicators displaying performance metrics,
 * animated in sequence with smooth arc animation and counting numbers.
 */

import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { CANVAS, INDICATORS, ANIMATION_TIMING } from './constants';
import { BackgroundRing } from './BackgroundRing';
import { CircularProgress } from './CircularProgress';
import { ProgressLabel } from './ProgressLabel';

export const AnimationSection03CircularProgressIndicators: React.FC = () => {
  return (
    <AbsoluteFill style={{ background: CANVAS.background }}>
      {/* Background rings - fade in at start */}
      <Sequence from={ANIMATION_TIMING.backgroundRingsFadeIn.start}>
        {INDICATORS.map((indicator, index) => (
          <BackgroundRing
            key={`bg-ring-${index}`}
            center={indicator.position}
            radius={indicator.radius}
            thickness={indicator.thickness}
            color={indicator.bgColor}
          />
        ))}
      </Sequence>

      {/* Circle 1 - Performance */}
      <Sequence from={ANIMATION_TIMING.circle1.start}>
        <CircularProgress
          center={INDICATORS[0].position}
          radius={INDICATORS[0].radius}
          thickness={INDICATORS[0].thickness}
          progress={INDICATORS[0].progress}
          color={INDICATORS[0].color}
          label={INDICATORS[0].label}
          duration={ANIMATION_TIMING.circle1.duration}
        />
      </Sequence>

      {/* Circle 2 - Reliability */}
      <Sequence from={ANIMATION_TIMING.circle2.start}>
        <CircularProgress
          center={INDICATORS[1].position}
          radius={INDICATORS[1].radius}
          thickness={INDICATORS[1].thickness}
          progress={INDICATORS[1].progress}
          color={INDICATORS[1].color}
          label={INDICATORS[1].label}
          duration={ANIMATION_TIMING.circle2.duration}
        />
      </Sequence>

      {/* Circle 3 - Efficiency */}
      <Sequence from={ANIMATION_TIMING.circle3.start}>
        <CircularProgress
          center={INDICATORS[2].position}
          radius={INDICATORS[2].radius}
          thickness={INDICATORS[2].thickness}
          progress={INDICATORS[2].progress}
          color={INDICATORS[2].color}
          label={INDICATORS[2].label}
          duration={ANIMATION_TIMING.circle3.duration}
        />
      </Sequence>

      {/* Labels - fade in early */}
      <Sequence from={ANIMATION_TIMING.labelsFadeIn.start}>
        {INDICATORS.map((indicator, index) => (
          <ProgressLabel
            key={`label-${index}`}
            position={[indicator.position[0], indicator.position[1] + 140]}
            label={indicator.label}
            duration={ANIMATION_TIMING.labelsFadeIn.duration}
          />
        ))}
      </Sequence>
    </AbsoluteFill>
  );
};

export default AnimationSection03CircularProgressIndicators;

export const defaultAnimationSection03CircularProgressIndicatorsProps = {};
