import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { BG, TOTAL_FRAMES, BEAT1_END, BEAT2_START, BEAT2_END, BEAT3_START } from './constants';
import { EngineeringGrid } from './EngineeringGrid';
import { Beat1Nozzle } from './Beat1Nozzle';
import { Beat2TwoGenerations } from './Beat2TwoGenerations';
import { Beat3CompressionRatio } from './Beat3CompressionRatio';

export const defaultPart3MoldThreeParts08PromptCapitalSpecificationProps = {};

/**
 * Section 3.8: Prompt Capital — The Specification That Governs
 *
 * Three visual beats across 600 frames (20s @ 30fps):
 *   Beat 1 (0-150):   Nozzle labels — text flows into mold nozzle
 *   Beat 2 (150-360):  Two generations — same spec, different code
 *   Beat 3 (360-600):  Compression ratio — prompt vs. code size comparison
 */
export const Part3MoldThreeParts08PromptCapitalSpecification: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Cross-fade transitions between beats ──

  // Beat 1 → Beat 2 transition (frames 140-170)
  const beat1FadeOut = interpolate(frame, [140, 165], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.quad),
  });

  // Beat 2 → Beat 3 transition (frames 340-370)
  const beat2FadeOut = interpolate(frame, [340, 365], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.quad),
  });

  return (
    <AbsoluteFill style={{ backgroundColor: BG }}>
      {/* Engineering grid — always visible */}
      <EngineeringGrid />

      {/* Beat 1: Nozzle Labels (frames 0 - 150) */}
      <Sequence from={0} durationInFrames={BEAT1_END + 20}>
        <AbsoluteFill style={{ opacity: beat1FadeOut }}>
          <Beat1Nozzle />
        </AbsoluteFill>
      </Sequence>

      {/* Beat 2: Two Generations (frames 150 - 360) */}
      <Sequence from={BEAT2_START} durationInFrames={BEAT2_END - BEAT2_START + 10}>
        <AbsoluteFill style={{ opacity: frame >= BEAT2_START ? beat2FadeOut : 0 }}>
          <Beat2TwoGenerations />
        </AbsoluteFill>
      </Sequence>

      {/* Beat 3: Compression Ratio (frames 360 - 600) */}
      <Sequence from={BEAT3_START} durationInFrames={TOTAL_FRAMES - BEAT3_START}>
        <Beat3CompressionRatio />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts08PromptCapitalSpecification;
