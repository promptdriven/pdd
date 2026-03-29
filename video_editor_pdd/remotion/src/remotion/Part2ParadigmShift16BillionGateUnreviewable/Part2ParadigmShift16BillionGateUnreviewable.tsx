import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { ChipLayout } from './ChipLayout';
import { CodeDiffScroll } from './CodeDiffScroll';

/*
 * Part2ParadigmShift16BillionGateUnreviewable
 *
 * Section 2.16: Billion Gates — Unreviewable
 * Duration: 360 frames @ 30fps (12s)
 *
 * First half: fractal chip layout with progressive zoom
 * Second half: scrolling code diff — equally overwhelming
 */

const BG_COLOR = '#0A0F1A';
const LABEL_COLOR = '#94A3B8';
const LABEL_FONT = 'Inter, sans-serif';
const LABEL_FONT_SIZE = 18;
const LABEL_FADE_FRAMES = 15;

const CHIP_DURATION = 150; // frames 0–149
const DIFF_START = 150; // frames 150–359
const DIFF_DURATION = 210;
const DIFF_DECEL_AT = 150; // local frame within diff phase (= global 300)

export const defaultPart2ParadigmShift16BillionGateUnreviewableProps = {};

export const Part2ParadigmShift16BillionGateUnreviewable: React.FC = () => {
  const frame = useCurrentFrame();

  // Label fade-in for chip view (frames 0-15)
  const chipLabelOpacity = interpolate(frame, [0, LABEL_FADE_FRAMES], [0, 0.9], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Label fade-in for diff view (frames 165-180, i.e. 15 frames after diff starts)
  const diffLabelOpacity = interpolate(
    frame,
    [DIFF_START + LABEL_FADE_FRAMES, DIFF_START + LABEL_FADE_FRAMES * 2],
    [0, 0.9],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const localDiffFrame = frame - DIFF_START;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* === CHIP LAYOUT PHASE (frames 0–149) === */}
      <Sequence from={0} durationInFrames={CHIP_DURATION} layout="none">
        <ChipLayout zoomStartFrame={0} zoomEndFrame={CHIP_DURATION} />

        {/* Chip gate count label */}
        <div
          style={{
            position: 'absolute',
            bottom: 60,
            right: 80,
            fontFamily: LABEL_FONT,
            fontSize: LABEL_FONT_SIZE,
            fontWeight: 400,
            color: LABEL_COLOR,
            opacity: chipLabelOpacity,
            letterSpacing: '0.02em',
            textShadow: '0 1px 4px rgba(0,0,0,0.6)',
          }}
        >
          2.1 billion gates
        </div>
      </Sequence>

      {/* === CODE DIFF PHASE (frames 150–359) === */}
      <Sequence from={DIFF_START} layout="none">
        <CodeDiffScroll
          localFrame={localDiffFrame}
          totalDuration={DIFF_DURATION}
          decelFrame={DIFF_DECEL_AT}
        />

        {/* Diff lines changed label */}
        <div
          style={{
            position: 'absolute',
            bottom: 60,
            right: 80,
            fontFamily: LABEL_FONT,
            fontSize: LABEL_FONT_SIZE,
            fontWeight: 400,
            color: LABEL_COLOR,
            opacity: diffLabelOpacity,
            letterSpacing: '0.02em',
            textShadow: '0 1px 4px rgba(0,0,0,0.6)',
          }}
        >
          47,382 lines changed
        </div>
      </Sequence>

      {/* Thin divider rule at bottom for visual grounding */}
      <div
        style={{
          position: 'absolute',
          bottom: 40,
          left: 80,
          right: 80,
          height: 2,
          backgroundColor: '#94A3B8',
          opacity: 0.7,
        }}
      />
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift16BillionGateUnreviewable;
