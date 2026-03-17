import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { BG_COLOR, TOTAL_FRAMES } from './constants';
import { ChartGrid } from './ChartGrid';
import { ChartAxes } from './ChartAxes';
import { AnimatedCurve } from './AnimatedCurve';
import { SawtoothLine } from './SawtoothLine';
import { GapGradient } from './GapGradient';
import { CISQCallout } from './CISQCallout';

export const defaultPart5CompoundReturns03CompoundDebtCurveProps = {};

export const Part5CompoundReturns03CompoundDebtCurve: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Grid lines (visible from frame 0) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ChartGrid />
      </Sequence>

      {/* Axes draw in from frame 0 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ChartAxes />
      </Sequence>

      {/* Exponential debt curve draws from frame 30 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <AnimatedCurve />
      </Sequence>

      {/* Sawtooth regeneration line draws from frame 90 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <SawtoothLine />
      </Sequence>

      {/* Gap gradient fills between curves from frame 210 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <GapGradient />
      </Sequence>

      {/* CISQ callout fades in from frame 210, number scales at 270 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <CISQCallout />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns03CompoundDebtCurve;
