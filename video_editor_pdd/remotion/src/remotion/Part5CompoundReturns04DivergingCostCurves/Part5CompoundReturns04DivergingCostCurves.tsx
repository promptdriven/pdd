import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  BG_COLOR,
  PATCHING_COLOR,
  PDD_COLOR,
  PATCHING_DATA,
  PDD_DATA,
  FONT_FAMILY,
  CURVE_DRAW_START,
  CURVE_DRAW_DURATION,
  CURVE_LABELS_START,
  CURVE_LABELS_FADE,
  THESIS_1_START,
  THESIS_2_START,
  THESIS_FADE,
  FADEOUT_START,
  FADEOUT_DURATION,
  CHART_RIGHT,
} from './constants';
import { ChartAxes } from './ChartAxes';
import { AnimatedLine, yToPixelCorrected } from './AnimatedLine';
import { GapRegion } from './GapRegion';

export const defaultPart5CompoundReturns04DivergingCostCurvesProps = {};

export const Part5CompoundReturns04DivergingCostCurves: React.FC = () => {
  const frame = useCurrentFrame();

  // Curve end labels fade in
  const curveLabelsOpacity = interpolate(
    frame,
    [CURVE_LABELS_START, CURVE_LABELS_START + CURVE_LABELS_FADE],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Thesis statement 1 fade in
  const thesis1Opacity = interpolate(
    frame,
    [THESIS_1_START, THESIS_1_START + THESIS_FADE],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Thesis statement 2 fade in
  const thesis2Opacity = interpolate(
    frame,
    [THESIS_2_START, THESIS_2_START + THESIS_FADE],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Final fade-out (entire chart dims to 0.3)
  const fadeOutOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0.3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // Pixel positions for curve end labels
  const patchingEndY = yToPixelCorrected(
    PATCHING_DATA[PATCHING_DATA.length - 1].y
  );
  const pddEndY = yToPixelCorrected(0.1); // PDD baseline

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: FONT_FAMILY,
      }}
    >
      <div style={{ opacity: fadeOutOpacity, width: '100%', height: '100%' }}>
        {/* Chart axes and grid */}
        <ChartAxes />

        {/* Patching exponential curve (amber) */}
        <AnimatedLine
          data={PATCHING_DATA}
          color={PATCHING_COLOR}
          strokeWidth={3}
          startFrame={CURVE_DRAW_START}
          drawDuration={CURVE_DRAW_DURATION}
          easingType="easeIn"
        />

        {/* PDD flat sawtooth curve (green) */}
        <AnimatedLine
          data={PDD_DATA}
          color={PDD_COLOR}
          strokeWidth={3}
          startFrame={CURVE_DRAW_START}
          drawDuration={CURVE_DRAW_DURATION}
          easingType="easeOut"
        />

        {/* Gap shaded region */}
        <GapRegion />

        {/* Curve end labels: "Patching" and "PDD" */}
        <div
          style={{
            position: 'absolute',
            left: CHART_RIGHT + 16,
            top: patchingEndY - 12,
            fontFamily: FONT_FAMILY,
            fontSize: 16,
            fontWeight: 600,
            color: PATCHING_COLOR,
            opacity: curveLabelsOpacity,
            whiteSpace: 'nowrap',
          }}
        >
          Patching
        </div>
        <div
          style={{
            position: 'absolute',
            left: CHART_RIGHT + 16,
            top: pddEndY - 12,
            fontFamily: FONT_FAMILY,
            fontSize: 16,
            fontWeight: 600,
            color: PDD_COLOR,
            opacity: curveLabelsOpacity,
            whiteSpace: 'nowrap',
          }}
        >
          PDD
        </div>

        {/* Thesis annotations below chart */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: 850,
            width: 1920,
            textAlign: 'center',
            fontFamily: FONT_FAMILY,
            fontSize: 18,
            fontWeight: 600,
            color: PATCHING_COLOR,
            opacity: thesis1Opacity,
          }}
        >
          Patching accrues compound costs.
        </div>
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: 890,
            width: 1920,
            textAlign: 'center',
            fontFamily: FONT_FAMILY,
            fontSize: 18,
            fontWeight: 600,
            color: PDD_COLOR,
            opacity: thesis2Opacity,
          }}
        >
          Tests accrue compound returns.
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns04DivergingCostCurves;
