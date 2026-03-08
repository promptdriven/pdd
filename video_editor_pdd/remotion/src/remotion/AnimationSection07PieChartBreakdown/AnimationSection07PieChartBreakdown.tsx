import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  interpolate,
  useCurrentFrame,
  Easing,
} from 'remotion';
import { CANVAS, PIE_DATA, TIMING } from './constants';
import { ChartTitle } from './ChartTitle';
import { PieSlice } from './PieSlice';
import { PercentageLabel } from './PercentageLabel';
import { Legend } from './Legend';

export const AnimationSection07PieChartBreakdown: React.FC = () => {
  const frame = useCurrentFrame();

  // Final rotation effect (frames 140-150)
  const rotationAngle = interpolate(
    frame,
    [TIMING.ROTATION_START, TIMING.ROTATION_START + 5, TIMING.ROTATION_START + TIMING.ROTATION_DURATION],
    [0, 2, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.BACKGROUND,
      }}
    >
      {/* Container with rotation effect */}
      <div
        style={{
          width: '100%',
          height: '100%',
          transform: `rotate(${rotationAngle}deg)`,
          transformOrigin: '700px 540px',
        }}
      >
        {/* Title (0-20 frames) */}
        <Sequence from={TIMING.TITLE_START} durationInFrames={TIMING.TOTAL_FRAMES}>
          <ChartTitle />
        </Sequence>

        {/* Pie Slices - each animates in sequence */}
        <Sequence from={TIMING.SLICE_1_START} durationInFrames={TIMING.TOTAL_FRAMES - TIMING.SLICE_1_START}>
          <PieSlice
            startAngle={PIE_DATA[0].startAngle}
            endAngle={PIE_DATA[0].endAngle}
            color={PIE_DATA[0].color}
            explode={PIE_DATA[0].explode}
          />
        </Sequence>

        <Sequence from={TIMING.SLICE_2_START} durationInFrames={TIMING.TOTAL_FRAMES - TIMING.SLICE_2_START}>
          <PieSlice
            startAngle={PIE_DATA[1].startAngle}
            endAngle={PIE_DATA[1].endAngle}
            color={PIE_DATA[1].color}
            explode={PIE_DATA[1].explode}
          />
        </Sequence>

        <Sequence from={TIMING.SLICE_3_START} durationInFrames={TIMING.TOTAL_FRAMES - TIMING.SLICE_3_START}>
          <PieSlice
            startAngle={PIE_DATA[2].startAngle}
            endAngle={PIE_DATA[2].endAngle}
            color={PIE_DATA[2].color}
            explode={PIE_DATA[2].explode}
          />
        </Sequence>

        <Sequence from={TIMING.SLICE_4_START} durationInFrames={TIMING.TOTAL_FRAMES - TIMING.SLICE_4_START}>
          <PieSlice
            startAngle={PIE_DATA[3].startAngle}
            endAngle={PIE_DATA[3].endAngle}
            color={PIE_DATA[3].color}
            explode={PIE_DATA[3].explode}
          />
        </Sequence>

        {/* Percentage Labels (100-120 frames) */}
        <Sequence from={TIMING.LABELS_START} durationInFrames={TIMING.LABELS_DURATION}>
          <svg
            width={CANVAS.WIDTH}
            height={CANVAS.HEIGHT}
            style={{
              position: 'absolute',
              top: 0,
              left: 0,
            }}
          >
            {PIE_DATA.map((slice, index) => {
              const midAngle = (slice.startAngle + slice.endAngle) / 2;
              return (
                <PercentageLabel
                  key={slice.id}
                  angle={midAngle}
                  percentage={slice.percentage}
                  color={slice.color}
                  index={index}
                />
              );
            })}
          </svg>
        </Sequence>

        {/* Legend (120-140 frames) */}
        <Sequence from={TIMING.LEGEND_START} durationInFrames={TIMING.LEGEND_DURATION}>
          <Legend items={PIE_DATA} />
        </Sequence>
      </div>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection07PieChartBreakdownProps = {};

export default AnimationSection07PieChartBreakdown;
