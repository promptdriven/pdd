import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  Easing,
  interpolate,
} from 'remotion';
import {
  BG_COLOR,
  CODE_DIM_START,
  CODE_DIM_END,
  CODE_UNDERLAY_TARGET_OPACITY,
} from './constants';
import { CodeUnderlay } from './CodeUnderlay';
import { QuestionText } from './QuestionText';
import { AccentLine } from './AccentLine';

export const defaultColdOpen06StillPatchingBeatProps = {};

/**
 * Section 0.6 — "So Why Are We Still Patching?" — The Beat
 *
 * A moment of deliberate stillness. The clean code from the previous shot
 * dims to near-invisible, and a single provocative question fades in at center.
 *
 * Duration: 150 frames (5s @ 30fps)
 *
 * Timeline:
 *   0–30:  Code dims from full to 0.08 opacity
 *  30–60:  Question text fades in
 *  75–90:  Accent line draws from center outward
 *  90–150: Hold — complete stillness
 */
export const ColdOpen06StillPatchingBeat: React.FC = () => {
  const frame = useCurrentFrame();

  // Code underlay dims from 1.0 → 0.08 over frames 0–30
  const codeOpacity = interpolate(
    frame,
    [CODE_DIM_START, CODE_DIM_END],
    [1.0, CODE_UNDERLAY_TARGET_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Dimmed code underlay — texture from previous shot */}
      <div style={{ opacity: codeOpacity }}>
        <CodeUnderlay />
      </div>

      {/* Question text — fades in frame 30–60 */}
      <QuestionText />

      {/* Accent line — draws frame 75–90 */}
      <AccentLine />
    </AbsoluteFill>
  );
};

export default ColdOpen06StillPatchingBeat;
