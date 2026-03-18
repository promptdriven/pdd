import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { EngineeringGrid } from './EngineeringGrid';
import { Beat1Nozzle } from './Beat1Nozzle';
import { Beat2TwoGenerations } from './Beat2TwoGenerations';
import { Beat3CompressionRatio } from './Beat3CompressionRatio';
import {
  COLORS,
  BEAT1_START,
  BEAT1_END,
  BEAT2_START,
  BEAT2_END,
  BEAT3_START,
  BEAT3_END,
} from './constants';

/**
 * Part3MoldThreeParts08PromptCapitalSpecification
 *
 * Section 3.8: Prompt Capital — The Specification That Governs
 * Duration: ~20s (600 frames @ 30fps)
 *
 * Three visual beats:
 * - Beat 1 (0-150): Nozzle labels — text flows into mold nozzle
 * - Beat 2 (150-360): Two generations — same prompt, different code, same behavior
 * - Beat 3 (360-600): Compression ratio — prompt vs code size, context window advantage
 */

export const defaultPart3MoldThreeParts08PromptCapitalSpecificationProps = {};

export const Part3MoldThreeParts08PromptCapitalSpecification: React.FC = () => {
  const frame = useCurrentFrame();

  // Cross-fade transitions between beats
  // Beat 1 fades out from frame 140-150
  const beat1Opacity = interpolate(frame, [140, 150], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Beat 2 fades out from frame 345-360
  const beat2Opacity = interpolate(frame, [345, 360], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        overflow: 'hidden',
      }}
    >
      {/* Engineering grid — always visible */}
      <EngineeringGrid />

      {/* Beat 1: Nozzle Labels (frames 0-150) */}
      <Sequence from={BEAT1_START} durationInFrames={BEAT1_END - BEAT1_START}>
        <AbsoluteFill style={{ opacity: beat1Opacity }}>
          <Beat1Nozzle />
        </AbsoluteFill>
      </Sequence>

      {/* Beat 2: Two Generations, Same Spec (frames 150-360) */}
      <Sequence from={BEAT2_START} durationInFrames={BEAT2_END - BEAT2_START}>
        <AbsoluteFill style={{ opacity: beat2Opacity }}>
          <Beat2TwoGenerations />
        </AbsoluteFill>
      </Sequence>

      {/* Beat 3: Compression Ratio (frames 360-600) */}
      <Sequence from={BEAT3_START} durationInFrames={BEAT3_END - BEAT3_START}>
        <Beat3CompressionRatio />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts08PromptCapitalSpecification;
