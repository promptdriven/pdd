import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { BG_COLOR, CLEARING_START, CLEARING_END } from './constants';
import { HorizontalLine } from './HorizontalLine';
import { InsightText } from './InsightText';

/**
 * Section 1.18 — Key Insight Stillness: "The 3B1B Beat"
 *
 * A deliberate moment of stillness — the palate cleanser between the
 * data-heavy economic argument and the synthesis that follows.
 * Near-black background, a barely-visible horizontal line, and quiet text.
 *
 * 360 frames @ 30fps = 12 seconds
 */

export const defaultPart1Economics18KeyInsightStillnessProps = {};

export const Part1Economics18KeyInsightStillness: React.FC = () => {
  const frame = useCurrentFrame();

  // Initial clearing overlay: simulates previous content fading to black.
  // A semi-transparent overlay fades from visible to gone over frames 0–60,
  // revealing the near-black background beneath.
  const clearingOverlayOpacity = interpolate(
    frame,
    [CLEARING_START, CLEARING_END],
    [0.6, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Clearing overlay — fades out to reveal the near-black canvas */}
      {clearingOverlayOpacity > 0.001 && (
        <AbsoluteFill
          style={{
            backgroundColor: '#0A0F1A',
            opacity: clearingOverlayOpacity,
          }}
        />
      )}

      {/* Horizontal line — draws from center outward starting at frame 60 */}
      <HorizontalLine />

      {/* Insight text — fades in at frame 90, holds, fades out at frame 300 */}
      <InsightText />
    </AbsoluteFill>
  );
};

export default Part1Economics18KeyInsightStillness;
