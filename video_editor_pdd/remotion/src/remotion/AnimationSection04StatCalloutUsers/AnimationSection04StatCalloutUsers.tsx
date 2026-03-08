/**
 * AnimationSection04StatCalloutUsers
 * User growth statistic callout with animated counter and progress ring
 *
 * Duration: 3s (90 frames at 30fps)
 * Features: Animated counter, circular progress ring, particles, glow effects
 */

import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { COLORS, ANIMATION } from './constants';
import { BackgroundGlow } from './BackgroundGlow';
import { ParticleSystem } from './ParticleSystem';
import { UserIcon } from './UserIcon';
import { PrefixText } from './PrefixText';
import { AnimatedCounter } from './AnimatedCounter';
import { ProgressRing } from './ProgressRing';
import { SuffixText } from './SuffixText';
import { PulseEffect } from './PulseEffect';

export const AnimationSection04StatCalloutUsers: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(circle at center, ${COLORS.BACKGROUND_CENTER} 0%, ${COLORS.BACKGROUND_EDGE} 100%)`,
        position: 'relative',
      }}
    >
      {/* Vignette effect */}
      <div
        style={{
          position: 'absolute',
          width: '100%',
          height: '100%',
          background: 'radial-gradient(circle at center, transparent 50%, rgba(0, 0, 0, 0.2) 100%)',
        }}
      />

      {/* Background glow - fades in frames 0-10 */}
      <Sequence from={0} durationInFrames={ANIMATION.TOTAL_FRAMES}>
        <BackgroundGlow />
      </Sequence>

      {/* Particle system - continuous throughout */}
      <Sequence from={0} durationInFrames={ANIMATION.TOTAL_FRAMES}>
        <ParticleSystem />
      </Sequence>

      {/* Main content with optional pulse effect */}
      <Sequence from={0} durationInFrames={ANIMATION.TOTAL_FRAMES}>
        {/* Pulse effect wrapper for frames 75-90 */}
        {(frame: number) => {
          const content = (
            <>
              {/* Icon drops in frames 10-25 */}
              <Sequence from={ANIMATION.ICON_START} durationInFrames={ANIMATION.ICON_DURATION}>
                <UserIcon />
              </Sequence>

              {/* Prefix text fades in frames 25-40 */}
              <Sequence from={ANIMATION.PREFIX_START} durationInFrames={ANIMATION.PREFIX_DURATION}>
                <PrefixText />
              </Sequence>

              {/* Counter and progress ring animate frames 30-75 */}
              <Sequence from={ANIMATION.COUNTER_START} durationInFrames={ANIMATION.COUNTER_DURATION}>
                <ProgressRing />
                <AnimatedCounter />
              </Sequence>

              {/* Suffix text fades in frames 50-70 */}
              <Sequence from={ANIMATION.SUFFIX_START} durationInFrames={ANIMATION.SUFFIX_DURATION}>
                <SuffixText />
              </Sequence>
            </>
          );

          // Apply pulse effect only during frames 75-90
          if (frame >= ANIMATION.PULSE_START) {
            return (
              <Sequence from={ANIMATION.PULSE_START} durationInFrames={ANIMATION.PULSE_DURATION}>
                <PulseEffect>{content}</PulseEffect>
              </Sequence>
            );
          }

          return content;
        }}
      </Sequence>
    </AbsoluteFill>
  );
};

export default AnimationSection04StatCalloutUsers;

export const defaultAnimationSection04StatCalloutUsersProps = {};
