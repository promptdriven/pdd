import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { COLORS, TIMING, PATCHING_POINTS, PDD_POINTS } from './constants';
import { ChartGrid } from './ChartGrid';
import { AnimatedCurve } from './AnimatedCurve';
import { GapFill } from './GapFill';
import { Annotations } from './Annotations';
import { GapLabel } from './GapLabel';

export const defaultPart5CompoundReturns04DivergingCostCurvesProps = {};

export const Part5CompoundReturns04DivergingCostCurves: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Grid, axes, and origin point — visible from frame 0 */}
      <Sequence from={0} durationInFrames={TIMING.totalDuration}>
        <ChartGrid />
      </Sequence>

      {/* Both curves draw from shared origin */}
      <Sequence from={0} durationInFrames={TIMING.totalDuration}>
        <AnimatedCurve
          points={PATCHING_POINTS}
          color={COLORS.patching}
          label="PATCHING"
        />
        <AnimatedCurve
          points={PDD_POINTS}
          color={COLORS.pdd}
          label="PDD"
        />
      </Sequence>

      {/* Gap gradient fill with pulse */}
      <Sequence from={0} durationInFrames={TIMING.totalDuration}>
        <GapFill />
      </Sequence>

      {/* Annotations */}
      <Sequence from={0} durationInFrames={TIMING.totalDuration}>
        <Annotations />
      </Sequence>

      {/* Gap label with double-arrow */}
      <Sequence from={0} durationInFrames={TIMING.totalDuration}>
        <GapLabel />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns04DivergingCostCurves;
