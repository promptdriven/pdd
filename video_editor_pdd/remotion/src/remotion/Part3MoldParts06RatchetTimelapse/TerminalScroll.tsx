import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TERMINAL_BG,
  TERMINAL_CHECK_COLOR,
  LABEL_TEXT_COLOR,
  TEST_LINES,
  CYCLE_FRAMES,
} from './constants';

const TERMINAL_WIDTH = 350;
const TERMINAL_HEIGHT = 160;
const LINE_HEIGHT = 16;
const VISIBLE_LINES = 8;

export const TerminalScroll: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine how many lines are visible.
  // Start with 5 lines (base walls), add one per cycle
  const baseLineCount = 5;
  let visibleLineCount = baseLineCount;
  for (let i = 0; i < 4; i++) {
    const cycleFrame = i * CYCLE_FRAMES + 28; // after flash + wall slide
    if (frame >= cycleFrame) {
      visibleLineCount++;
    }
  }
  visibleLineCount = Math.min(visibleLineCount, TEST_LINES.length);

  // Calculate scroll offset to keep latest lines visible
  const scrollOffset = Math.max(0, visibleLineCount - VISIBLE_LINES) * LINE_HEIGHT;

  // Use scrollOffset directly — no need for interpolate here
  const smoothScroll = scrollOffset;

  return (
    <div
      style={{
        position: 'absolute',
        right: 70,
        bottom: 40,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        opacity: 0.9,
        borderRadius: 8,
        overflow: 'hidden',
        border: '1px solid rgba(100, 116, 139, 0.3)',
      }}
    >
      {/* Terminal header */}
      <div
        style={{
          padding: '6px 12px',
          borderBottom: '1px solid rgba(100, 116, 139, 0.2)',
          display: 'flex',
          alignItems: 'center',
          gap: 6,
        }}
      >
        <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#EF4444' }} />
        <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#F59E0B' }} />
        <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#22C55E' }} />
        <span
          style={{
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 10,
            color: LABEL_TEXT_COLOR,
            opacity: 0.5,
            marginLeft: 8,
          }}
        >
          pdd test
        </span>
      </div>

      {/* Scrolling content */}
      <div
        style={{
          padding: '6px 12px',
          height: TERMINAL_HEIGHT - 32,
          overflow: 'hidden',
          position: 'relative',
        }}
      >
        <div
          style={{
            transform: `translateY(-${smoothScroll}px)`,
            transition: 'transform 0.3s ease-out',
          }}
        >
          {TEST_LINES.slice(0, visibleLineCount).map((line, i) => {
            // Fade in animation for new lines
            const lineAppearFrame =
              i < baseLineCount ? 0 : (i - baseLineCount) * CYCLE_FRAMES + 28;
            const lineLocalFrame = frame - lineAppearFrame;
            const lineOpacity =
              lineLocalFrame < 0
                ? 0
                : interpolate(Math.min(lineLocalFrame, 10), [0, 10], [0, 1], {
                    extrapolateRight: 'clamp',
                    easing: Easing.out(Easing.quad),
                  });

            return (
              <div
                key={i}
                style={{
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 11,
                  lineHeight: `${LINE_HEIGHT}px`,
                  color: TERMINAL_CHECK_COLOR,
                  whiteSpace: 'nowrap',
                  opacity: lineOpacity,
                }}
              >
                {line}
              </div>
            );
          })}
        </div>
      </div>
    </div>
  );
};
