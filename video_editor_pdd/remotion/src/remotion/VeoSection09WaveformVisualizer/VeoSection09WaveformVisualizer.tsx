import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { NoiseGrain } from './NoiseGrain';
import { SectionLabel } from './SectionLabel';
import { WaveformBars } from './WaveformBars';
import { TimelineScrubber } from './TimelineScrubber';
import { TimestampCounter } from './TimestampCounter';

export const VeoSection09WaveformVisualizer: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      <NoiseGrain />
      <SectionLabel />
      <WaveformBars />
      <TimelineScrubber />
      <TimestampCounter />
    </AbsoluteFill>
  );
};

export const defaultVeoSection09WaveformVisualizerProps = {};

export default VeoSection09WaveformVisualizer;
