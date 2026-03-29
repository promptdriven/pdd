import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { BG_COLOR, TOTAL_FRAMES } from './constants';
import { ChartAxes } from './ChartAxes';
import { AnimatedCurve } from './AnimatedCurve';
import { GreenLine } from './GreenLine';
import { ResetArrows } from './ResetArrows';
import { FormulaLabel, FlatLineLabel, CISQCallout } from './Labels';

export const defaultPart5CompoundReturns03CompoundDebtCurveProps = {};

export const Part5CompoundReturns03CompoundDebtCurve: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {/* Axes and grid — visible from frame 0 */}
        <ChartAxes />

        {/* Amber exponential debt curve — draws from frame 30-180 */}
        <AnimatedCurve />

        {/* Formula label — fades in at frame 90 */}
        <FormulaLabel />

        {/* Green flat regeneration line — draws from frame 180-270 */}
        <GreenLine />

        {/* Reset arrows on green line — staggered from frame 210 */}
        <ResetArrows />

        {/* Flat line label — fades in at frame 270 */}
        <FlatLineLabel />

        {/* CISQ callout — fades in at frame 330 */}
        <CISQCallout />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns03CompoundDebtCurve;
