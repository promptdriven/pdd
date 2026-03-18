import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import { BG_COLOR, SPLIT_LINE_COLOR, SPLIT_LINE_OPACITY, SPLIT_X } from './constants';
import { LeftPanel } from './LeftPanel';
import { RightPanel } from './RightPanel';

export const defaultPart1Economics07SplitContextComparisonProps = {};

export const Part1Economics07SplitContextComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Split line appears: frames 0-30
  const splitLineOpacity = interpolate(frame, [0, 30], [0, SPLIT_LINE_OPACITY], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
        overflow: 'hidden',
      }}
    >
      {/* Left panel — Agentic Patching */}
      <LeftPanel />

      {/* Vertical split divider */}
      <div
        style={{
          position: 'absolute',
          left: SPLIT_X - 1,
          top: 0,
          width: 2,
          height: 1080,
          backgroundColor: SPLIT_LINE_COLOR,
          opacity: splitLineOpacity,
        }}
      />

      {/* Right panel — PDD Regeneration */}
      <RightPanel />
    </AbsoluteFill>
  );
};

export default Part1Economics07SplitContextComparison;
