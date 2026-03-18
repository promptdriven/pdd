import React from 'react';
import { AbsoluteFill } from 'remotion';
import {
  BG_COLOR,
  PATCHING_COLOR,
  PDD_COLOR,
  PATCHING_POINTS,
  PDD_POINTS,
} from './constants';
import { ChartGrid } from './ChartGrid';
import { ChartAxes } from './ChartAxes';
import { AnimatedCurve } from './AnimatedCurve';
import { GapFill } from './GapFill';
import { Annotations } from './Annotations';
import { GapLabel } from './GapLabel';

export const defaultPart5CompoundReturns04DivergingCostCurvesProps = {};

/**
 * Section 5.4: Diverging Cost Curves — The Compounding Gap
 *
 * Two cost curves (Patching vs PDD) draw from a shared origin and diverge
 * dramatically over 10 years, visualizing the compound cost argument.
 *
 * Duration: 420 frames @ 30fps (14s)
 *
 * All sub-components manage their own timing via absolute frame references
 * from useCurrentFrame() (no Sequence offset wrappers).
 */
export const Part5CompoundReturns04DivergingCostCurves: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
        overflow: 'hidden',
      }}
    >
      {/* Layer 1: Subtle background grid */}
      <ChartGrid />

      {/* Layer 2: Axes + origin point + labels */}
      <ChartAxes />

      {/* Layer 3: Patching curve (exponential rise) */}
      <AnimatedCurve
        points={PATCHING_POINTS}
        color={PATCHING_COLOR}
        label="PATCHING"
      />

      {/* Layer 4: PDD curve (flat/declining) */}
      <AnimatedCurve
        points={PDD_POINTS}
        color={PDD_COLOR}
        label="PDD"
      />

      {/* Layer 5: Gradient fill between curves with pulse */}
      <GapFill />

      {/* Layer 6: Side annotations with leader lines */}
      <Annotations />

      {/* Layer 7: Central "compounding gap" label + double arrow */}
      <GapLabel />
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns04DivergingCostCurves;
