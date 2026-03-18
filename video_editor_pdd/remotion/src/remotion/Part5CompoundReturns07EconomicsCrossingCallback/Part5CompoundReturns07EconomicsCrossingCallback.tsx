import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import {
  BG_COLOR,
  WIDTH, HEIGHT,
  FADE_IN_END,
  TOTAL_FRAMES,
  LABOR_COST_DATA, SOCK_COST_DATA,
  PATCHING_COST_DATA, GENERATION_COST_DATA,
  AMBER, BLUE,
  INITIAL_LINE1_LABEL, FINAL_LINE1_LABEL,
  INITIAL_LINE2_LABEL, FINAL_LINE2_LABEL,
} from './constants';
import {ChartAxes} from './ChartAxes';
import {AnimatedLine} from './AnimatedLine';
import {ShadedZones} from './ShadedZones';
import {CrossingPoint} from './CrossingPoint';
import {DarningNeedle} from './DarningNeedle';

export const defaultPart5CompoundReturns07EconomicsCrossingCallbackProps = {};

/**
 * Section 5.7: Economics Crossing Callback — The Chart Returns
 *
 * The sock economics chart from Part 1 returns, then morphs into
 * a code economics chart. Same crossing, different domain.
 * ~10s (300 frames @ 30fps)
 */
export const Part5CompoundReturns07EconomicsCrossingCallback: React.FC = () => {
  const frame = useCurrentFrame();

  // Entire chart fades in over first 30 frames (easeOut quad)
  const fadeIn = interpolate(frame, [0, FADE_IN_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* Chart content with fade-in */}
      <AbsoluteFill style={{opacity: fadeIn}}>
        {/* Shaded zones (green pre-crossing, red post-crossing) */}
        <ShadedZones />

        {/* Grid, axes, and labels */}
        <ChartAxes />

        {/* Amber line: Labor cost → Patching cost */}
        <AnimatedLine
          initialData={LABOR_COST_DATA}
          finalData={PATCHING_COST_DATA}
          initialXRange={[1950, 2020]}
          finalXRange={[2020, 2030]}
          color={AMBER}
          initialLabel={INITIAL_LINE1_LABEL}
          finalLabel={FINAL_LINE1_LABEL}
          labelYOffset={-8}
        />

        {/* Blue line: Sock cost → Generation cost */}
        <AnimatedLine
          initialData={SOCK_COST_DATA}
          finalData={GENERATION_COST_DATA}
          initialXRange={[1950, 2020]}
          finalXRange={[2020, 2030]}
          color={BLUE}
          initialLabel={INITIAL_LINE2_LABEL}
          finalLabel={FINAL_LINE2_LABEL}
          labelYOffset={8}
        />

        {/* Crossing point with pulse, label, and post-crossing label */}
        <CrossingPoint />

        {/* Darning needle strikethrough — the punchline */}
        <DarningNeedle />
      </AbsoluteFill>

      {/* Title bar — subtle "Economics" header */}
      <div
        style={{
          position: 'absolute',
          top: 40,
          left: 0,
          right: 0,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 16,
          fontWeight: 500,
          color: '#64748B',
          opacity: fadeIn * 0.6,
          letterSpacing: '0.08em',
          textTransform: 'uppercase',
        }}
      >
        Economics of Replacement
      </div>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns07EconomicsCrossingCallback;
