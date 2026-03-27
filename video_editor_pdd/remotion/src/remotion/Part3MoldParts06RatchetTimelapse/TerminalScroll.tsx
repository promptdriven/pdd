import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_BG,
  TERMINAL_CHECK_COLOR,
  WALL_LABEL_COLOR,
  TEST_LINES,
  CYCLE_FRAMES,
} from './constants';

export const TerminalScroll: React.FC = () => {
  const frame = useCurrentFrame();

  // Base visible lines: first 5 appear immediately (representing pre-existing tests)
  // Then new lines appear every CYCLE_FRAMES after the first few
  const baseVisibleCount = 5;
  const additionalLines = Math.floor(frame / CYCLE_FRAMES);
  const visibleCount = Math.min(TEST_LINES.length, baseVisibleCount + additionalLines);

  // Show only the last N lines that fit in the terminal
  const maxVisibleLines = 7;
  const startIndex = Math.max(0, visibleCount - maxVisibleLines);
  const visibleLines = TEST_LINES.slice(startIndex, visibleCount);

  // Scroll offset for smooth scrolling
  const scrollOffset =
    startIndex > 0
      ? interpolate(
          frame % CYCLE_FRAMES,
          [0, Math.min(15, CYCLE_FRAMES)],
          [0, 0],
          { extrapolateRight: 'clamp' }
        )
      : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL_X,
        top: TERMINAL_Y,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        opacity: 0.85,
        borderRadius: 6,
        overflow: 'hidden',
        padding: '8px 12px',
        border: '1px solid #2A2A3E',
      }}
    >
      {/* Terminal header */}
      <div
        style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 10,
          color: WALL_LABEL_COLOR,
          opacity: 0.5,
          marginBottom: 6,
          borderBottom: '1px solid #2A2A3E',
          paddingBottom: 4,
        }}
      >
        $ pdd test
      </div>

      {/* Scrolling test lines */}
      <div
        style={{
          transform: `translateY(${scrollOffset}px)`,
          display: 'flex',
          flexDirection: 'column',
          gap: 2,
        }}
      >
        {visibleLines.map((line, i) => {
          const globalIndex = startIndex + i;
          const lineAppearFrame =
            globalIndex < baseVisibleCount
              ? globalIndex * 4 // stagger base lines over first ~20 frames
              : (globalIndex - baseVisibleCount) * CYCLE_FRAMES + 20;

          const lineOpacity = interpolate(
            frame - lineAppearFrame,
            [0, 8],
            [0, 1],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            }
          );

          return (
            <div
              key={`line-${globalIndex}`}
              style={{
                fontFamily: 'JetBrains Mono, monospace',
                fontSize: 11,
                color: TERMINAL_CHECK_COLOR,
                opacity: lineOpacity,
                whiteSpace: 'nowrap',
                lineHeight: '16px',
              }}
            >
              {line}
            </div>
          );
        })}
      </div>
    </div>
  );
};
