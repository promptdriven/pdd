import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import {
  BG_COLOR,
  CURVE_START,
  SAWTOOTH_START,
  GAP_FILL_START,
  CALLOUT_FADE_START,
  DURATION_FRAMES,
} from './constants';
import { ChartGrid } from './ChartGrid';
import { ChartAxes } from './ChartAxes';
import { ExponentialCurve, FormulaLabel } from './ExponentialCurve';
import { SawtoothLine } from './SawtoothLine';
import { GapGradient } from './GapGradient';
import { CISQCallout } from './CISQCallout';

export const defaultPart5CompoundReturns03CompoundDebtCurveProps = {};

export const Part5CompoundReturns03CompoundDebtCurve: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Grid and Axes — visible from frame 0 */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <ChartGrid />
        <ChartAxes />
      </Sequence>

      {/* Exponential debt curve — starts at frame 30 */}
      <Sequence from={CURVE_START} durationInFrames={DURATION_FRAMES - CURVE_START}>
        <ExponentialCurve />
      </Sequence>

      {/* Formula label types in at frame 120 (90 frames into curve sequence) */}
      <Sequence from={CURVE_START + 90} durationInFrames={DURATION_FRAMES - (CURVE_START + 90)}>
        <FormulaLabel />
      </Sequence>

      {/* Sawtooth regeneration line — starts at frame 90 */}
      <Sequence from={SAWTOOTH_START} durationInFrames={DURATION_FRAMES - SAWTOOTH_START}>
        <SawtoothLine />
      </Sequence>

      {/* Gap gradient fill — starts at frame 210 */}
      <Sequence from={GAP_FILL_START} durationInFrames={DURATION_FRAMES - GAP_FILL_START}>
        <GapGradient />
      </Sequence>

      {/* CISQ callout — starts at frame 210 */}
      <Sequence from={CALLOUT_FADE_START} durationInFrames={DURATION_FRAMES - CALLOUT_FADE_START}>
        <CISQCallout />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns03CompoundDebtCurve;
