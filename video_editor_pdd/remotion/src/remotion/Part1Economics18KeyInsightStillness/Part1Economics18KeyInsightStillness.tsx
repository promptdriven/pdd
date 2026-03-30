import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { BG_NEAR_BLACK } from './constants';
import { HorizontalLine } from './HorizontalLine';
import { InsightText } from './InsightText';

export const defaultPart1Economics18KeyInsightStillnessProps = {};

/**
 * Section 1.18 — Key Insight Stillness
 *
 * A deliberate "3Blue1Brown beat": the screen clears to near-black,
 * a thin horizontal line draws from center, and a quiet text appears
 * before fading out. The stillness *is* the content.
 *
 * 360 frames @ 30 fps (12 s)
 *
 * Timeline:
 *   0–60    Background darken / clearing overlay fades out
 *  60–90    Line draws from center outward
 *  90–150   Text fades in
 * 150–300   Hold — deliberate stillness
 * 300–330   Text fades out
 * 330–360   Line holds, transition beat
 */
export const Part1Economics18KeyInsightStillness: React.FC = () => {
  const frame = useCurrentFrame();

  // Clearing overlay: starts opaque (simulating previous scene remnant),
  // fades to 0 over first 60 frames so the near-black background is revealed.
  const clearingOpacity = interpolate(frame, [0, 60], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.cubic),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_NEAR_BLACK,
        overflow: 'hidden',
      }}
    >
      {/* Clearing overlay — fades from a slightly lighter dark to nothing */}
      <AbsoluteFill
        style={{
          backgroundColor: '#0A0F1A',
          opacity: clearingOpacity,
        }}
      />

      {/* Horizontal center line (draws 60–90) */}
      <HorizontalLine />

      {/* Insight text (fades in 90–150, holds, fades out 300–330) */}
      <InsightText />
    </AbsoluteFill>
  );
};

export default Part1Economics18KeyInsightStillness;
