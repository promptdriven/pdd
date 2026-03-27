// Part2ParadigmShift16BillionGateUnreviewable.tsx
// Section 2.16: Billion Gates — Unreviewable
// Duration: ~12s (360 frames @ 30fps)
//
// A dense chip layout zooms in fractally, then hard-cuts to a fast-scrolling
// code diff — both visually overwhelming and unreviewable.

import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
} from 'remotion';
import { ChipLayout } from './ChipLayout';
import { CodeDiffScroll } from './CodeDiffScroll';

const BG_COLOR = '#0A0F1A';
const CHIP_DURATION = 150; // frames 0–149
const DIFF_START = 150;
const DIFF_DURATION = 210; // frames 150–359

export const defaultPart2ParadigmShift16BillionGateUnreviewableProps = {};

export const Part2ParadigmShift16BillionGateUnreviewable: React.FC = () => {
  const frame = useCurrentFrame();

  // Hard cut: chip visible for first 150 frames, diff for rest
  const showChip = frame < CHIP_DURATION;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
        overflow: 'hidden',
      }}
    >
      {/* Chip layout with fractal zoom — frames 0-149 */}
      {showChip && (
        <Sequence from={0} durationInFrames={CHIP_DURATION}>
          <AbsoluteFill>
            {/* Inside Sequence, useCurrentFrame() is 0-based relative to this sequence */}
            <ChipLayout startFrame={0} durationInFrames={CHIP_DURATION} />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Code diff scroll — frames 150-359 */}
      {!showChip && (
        <Sequence from={DIFF_START} durationInFrames={DIFF_DURATION}>
          <AbsoluteFill>
            {/* Sequence offsets frame to 0-based; pass startFrame=0 accordingly */}
            <CodeDiffScroll
              startFrame={0}
              durationInFrames={DIFF_DURATION}
            />
          </AbsoluteFill>
        </Sequence>
      )}
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift16BillionGateUnreviewable;
