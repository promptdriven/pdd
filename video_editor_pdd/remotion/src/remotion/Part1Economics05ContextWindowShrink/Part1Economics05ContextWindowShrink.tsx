import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
} from 'remotion';
import {
  BG_COLOR,
  TOTAL_FRAMES,
  GRID_START,
  HIGHLIGHTS_START,
  INSET_START,
} from './constants';
import { CodebaseGrid } from './CodebaseGrid';
import { ContextWindow } from './ContextWindow';
import { CoverageCounter } from './CoverageCounter';
import { BlockHighlights } from './BlockHighlights';
import { InsetGraph } from './InsetGraph';

export const defaultPart1Economics05ContextWindowShrinkProps = {};

export const Part1Economics05ContextWindowShrink: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 0-30: previous chart fades out (we show darkening bg)
  const initialOverlayOpacity = interpolate(frame, [0, 30], [0.3, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Subtle initial overlay to suggest previous content fading */}
      {frame < 30 && (
        <AbsoluteFill
          style={{
            backgroundColor: `rgba(13, 17, 23, ${1 - initialOverlayOpacity})`,
            zIndex: 50,
          }}
        />
      )}

      {/* Title that appears briefly to orient */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <div
          style={{
            position: 'absolute',
            left: 80,
            top: 40,
            fontFamily: 'Inter, sans-serif',
            fontSize: 18,
            fontWeight: 600,
            color: '#E2E8F0',
            opacity: interpolate(frame, [30, 50, 800, 870], [0, 0.4, 0.4, 0], {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
            }),
            letterSpacing: '0.05em',
          }}
        >
          The AI Blindspot
        </div>
      </Sequence>

      {/* Codebase grid — morphing through stages */}
      <Sequence from={GRID_START} durationInFrames={TOTAL_FRAMES - GRID_START}>
        <CodebaseGrid />
      </Sequence>

      {/* Fixed-size context window overlay */}
      <Sequence from={GRID_START} durationInFrames={TOTAL_FRAMES - GRID_START}>
        <ContextWindow />
      </Sequence>

      {/* Coverage counter */}
      <Sequence from={GRID_START} durationInFrames={TOTAL_FRAMES - GRID_START}>
        <CoverageCounter />
      </Sequence>

      {/* Red/green highlight blocks */}
      <Sequence from={HIGHLIGHTS_START} durationInFrames={TOTAL_FRAMES - HIGHLIGHTS_START}>
        <BlockHighlights />
      </Sequence>

      {/* Inset performance graph */}
      <Sequence from={INSET_START} durationInFrames={TOTAL_FRAMES - INSET_START}>
        <InsetGraph />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics05ContextWindowShrink;
