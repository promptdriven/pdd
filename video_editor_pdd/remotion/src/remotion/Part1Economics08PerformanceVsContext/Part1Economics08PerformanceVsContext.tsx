import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { BG_COLOR, TOTAL_FRAMES } from './constants';
import { BackgroundGrid } from './BackgroundGrid';
import { InsetChart } from './InsetChart';
import { DebtAreaPulse } from './DebtAreaPulse';

export const defaultPart1Economics08PerformanceVsContextProps = {};

/**
 * Section 1.8: Performance vs. Context Length — EMNLP Study Inset
 *
 * Animation sequence (1470 frames @ 30fps, ~49s):
 *   0-60    Grid dims to 30%, inset border draws in
 *   60-90   Inset bg fills, title types in
 *   90-210  Axes draw, declining performance line animates
 *   210-360 Hold on inset, labels appear
 *   360-600 Hold — narration covers EMNLP study
 *   600-720 Inset fades out, code cost chart fades in
 *   720-900 Context Rot layer pulses, annotation appears
 *   900-1470 Hold with pulsing debt area
 */
export const Part1Economics08PerformanceVsContext: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Layer 1: Dimming context grid background (full duration) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="BackgroundGrid">
        <BackgroundGrid />
      </Sequence>

      {/* Layer 2: Inset performance chart (frames 0–720, fades itself out) */}
      <Sequence from={0} durationInFrames={720} name="InsetChart">
        <InsetChart />
      </Sequence>

      {/* Layer 3: Code cost chart with debt area pulse (frames 600–end) */}
      <Sequence
        from={600}
        durationInFrames={TOTAL_FRAMES - 600}
        name="DebtAreaPulse"
      >
        <DebtAreaPulse />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics08PerformanceVsContext;
