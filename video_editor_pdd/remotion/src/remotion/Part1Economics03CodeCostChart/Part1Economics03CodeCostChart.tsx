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
  BLUE_LINE_COLOR,
  AMBER_LINE_COLOR,
  GENERATE_COST_DATA,
  IMMEDIATE_PATCH_DATA,
  TOTAL_COST_DEBT_DATA,
  TOTAL_FRAMES,
  BLUE_LINE_START,
  BLUE_LINE_END,
  AMBER_SOLID_START,
  AMBER_SOLID_END,
  PULSE_START,
  PULSE_END,
  DASHED_LINE_START,
  DASHED_LINE_END,
  PULLBACK_START,
  PULLBACK_END,
} from './constants';
import { ChartAxes } from './ChartAxes';
import { AnimatedLine } from './AnimatedLine';
import { DateMarkers } from './DateMarkers';
import { DebtArea } from './DebtArea';
import { Legend } from './Legend';

export const defaultPart1Economics03CodeCostChartProps = {};

export const Part1Economics03CodeCostChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Camera pullback: scale from 1.0 to 0.85 starting at frame 600
  const scale = interpolate(frame, [PULLBACK_START, PULLBACK_END], [1.0, 0.85], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  // Translate to keep chart centered during scale
  const translateX = ((1 - scale) * 1920) / 2;
  const translateY = ((1 - scale) * 1080) / 2;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      <div
        style={{
          position: 'absolute',
          width: 1920,
          height: 1080,
          transform: `translate(${translateX}px, ${translateY}px) scale(${scale})`,
          transformOrigin: 'top left',
        }}
      >
        {/* Chart axes — visible from frame 0 */}
        <ChartAxes />

        {/* Blue "cost to generate" line */}
        <Sequence from={BLUE_LINE_START} durationInFrames={TOTAL_FRAMES - BLUE_LINE_START}>
          <AnimatedLine
            lineId="generate"
            data={GENERATE_COST_DATA}
            color={BLUE_LINE_COLOR}
            strokeWidth={3}
            drawStart={0}
            drawEnd={BLUE_LINE_END - BLUE_LINE_START}
          />
        </Sequence>

        {/* Date markers — appear as blue line passes each year */}
        <Sequence from={BLUE_LINE_START} durationInFrames={TOTAL_FRAMES - BLUE_LINE_START}>
          <DateMarkers
            blueLineStart={0}
            blueLineEnd={BLUE_LINE_END - BLUE_LINE_START}
          />
        </Sequence>

        {/* Amber solid "immediate patch cost" line */}
        <Sequence from={AMBER_SOLID_START} durationInFrames={TOTAL_FRAMES - AMBER_SOLID_START}>
          <AnimatedLine
            lineId="patch"
            data={IMMEDIATE_PATCH_DATA}
            color={AMBER_LINE_COLOR}
            strokeWidth={3}
            drawStart={0}
            drawEnd={AMBER_SOLID_END - AMBER_SOLID_START}
            glowActive
            glowStart={PULSE_START - AMBER_SOLID_START}
            glowEnd={PULSE_END - AMBER_SOLID_START}
          />
        </Sequence>

        {/* Amber dashed "total cost with debt" line */}
        <Sequence from={DASHED_LINE_START} durationInFrames={TOTAL_FRAMES - DASHED_LINE_START}>
          <AnimatedLine
            lineId="debt"
            data={TOTAL_COST_DEBT_DATA}
            color={AMBER_LINE_COLOR}
            strokeWidth={2.5}
            drawStart={0}
            drawEnd={DASHED_LINE_END - DASHED_LINE_START}
            dashPattern="8 6"
          />
        </Sequence>

        {/* Shaded debt area between dashed and solid amber lines */}
        <Sequence from={DASHED_LINE_START} durationInFrames={TOTAL_FRAMES - DASHED_LINE_START}>
          <DebtArea
            fillStart={0}
            fillDuration={DASHED_LINE_END - DASHED_LINE_START}
          />
        </Sequence>

        {/* Legend */}
        <Legend appearFrame={DASHED_LINE_END} />
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics03CodeCostChart;
