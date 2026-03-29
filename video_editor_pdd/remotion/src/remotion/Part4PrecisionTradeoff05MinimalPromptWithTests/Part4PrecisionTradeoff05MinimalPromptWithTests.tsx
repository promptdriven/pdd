import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import {
  BG_COLOR,
  WINDOW_FRAME_COLOR,
  TITLE_BAR_COLOR,
  FILENAME_COLOR,
  PROMPT_TEXT_COLOR,
  BLUE_ACCENT,
  GREEN_ACCENT,
  EDITOR_X,
  EDITOR_Y,
  EDITOR_WIDTH,
  EDITOR_HEIGHT,
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TITLE_BAR_HEIGHT,
  WINDOW_BORDER_RADIUS,
  EDITOR_FADE_DURATION,
  TERMINAL_FADE_START,
  TERMINAL_FADE_DURATION,
  TEST_CASCADE_START,
  TEST_COUNT,
  TESTS_PER_FRAME,
  WALLS_START,
  SUMMARY_START,
  LABEL_FADE_START,
  LABEL_FADE_DURATION,
  FADEOUT_START,
  FADEOUT_DURATION,
  TOTAL_FRAMES,
  PROMPT_LINES,
  TEST_NAMES,
  FONT_MONO,
  FONT_SANS,
} from './constants';
import { TestWalls } from './TestWalls';

// ─── Default Props ───────────────────────────────────────────────
export const defaultPart4PrecisionTradeoff05MinimalPromptWithTestsProps = {};

// ─── Editor Window ───────────────────────────────────────────────
const EditorWindow: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, EDITOR_FADE_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: EDITOR_X,
        top: EDITOR_Y,
        width: EDITOR_WIDTH,
        height: EDITOR_HEIGHT,
        opacity,
        borderRadius: WINDOW_BORDER_RADIUS,
        border: `1px solid ${WINDOW_FRAME_COLOR}`,
        backgroundColor: WINDOW_FRAME_COLOR,
        boxShadow: `0 0 12px rgba(74, 144, 217, 0.1)`,
        overflow: 'hidden',
      }}
    >
      {/* Title Bar */}
      <div
        style={{
          height: TITLE_BAR_HEIGHT,
          backgroundColor: TITLE_BAR_COLOR,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'space-between',
          padding: '0 14px',
        }}
      >
        {/* Traffic lights */}
        <div style={{ display: 'flex', gap: 6 }}>
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: '50%',
              backgroundColor: '#FF5F57',
              opacity: 0.7,
            }}
          />
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: '50%',
              backgroundColor: '#FEBC2E',
              opacity: 0.7,
            }}
          />
          <div
            style={{
              width: 10,
              height: 10,
              borderRadius: '50%',
              backgroundColor: '#28C840',
              opacity: 0.7,
            }}
          />
        </div>

        {/* Filename */}
        <div
          style={{
            fontFamily: FONT_MONO,
            fontSize: 13,
            color: FILENAME_COLOR,
          }}
        >
          parser_v2.prompt
        </div>

        {/* Badge */}
        <div
          style={{
            fontFamily: FONT_SANS,
            fontSize: 11,
            fontWeight: 600,
            color: BLUE_ACCENT,
            backgroundColor: 'rgba(74, 144, 217, 0.15)',
            padding: '2px 8px',
            borderRadius: 4,
          }}
        >
          10 lines
        </div>
      </div>

      {/* Prompt Content */}
      <div
        style={{
          padding: '10px 16px',
          display: 'flex',
          flexDirection: 'column',
          gap: 2,
        }}
      >
        {PROMPT_LINES.map((line, i) => (
          <div
            key={i}
            style={{
              display: 'flex',
              alignItems: 'center',
              gap: 12,
            }}
          >
            <span
              style={{
                fontFamily: FONT_MONO,
                fontSize: 12,
                color: '#475569',
                width: 20,
                textAlign: 'right',
                flexShrink: 0,
              }}
            >
              {i + 1}
            </span>
            <span
              style={{
                fontFamily: FONT_MONO,
                fontSize: 13,
                color: PROMPT_TEXT_COLOR,
                whiteSpace: 'nowrap',
              }}
            >
              {line}
            </span>
          </div>
        ))}
      </div>
    </div>
  );
};

// ─── Terminal Window ─────────────────────────────────────────────
const TerminalWindow: React.FC = () => {
  const frame = useCurrentFrame();

  // Terminal appears at TERMINAL_FADE_START
  const terminalOpacity = interpolate(
    frame,
    [TERMINAL_FADE_START, TERMINAL_FADE_START + TERMINAL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Typewriter: "$ pdd test parser" types in from frame 60-90
  const commandText = '$ pdd test parser';
  const typedChars = interpolate(
    frame,
    [TERMINAL_FADE_START, TERMINAL_FADE_START + 25],
    [0, commandText.length],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );
  const displayedCommand = commandText.slice(0, Math.floor(typedChars));

  // Test cascade: starts at TEST_CASCADE_START
  const visibleTests = Math.min(
    TEST_COUNT,
    Math.max(0, Math.floor((frame - TEST_CASCADE_START) * TESTS_PER_FRAME))
  );

  // Summary: appears at SUMMARY_START
  const summaryOpacity = interpolate(
    frame,
    [SUMMARY_START, SUMMARY_START + 15],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Determine visible test window (scrolling effect)
  const maxVisibleRows = 18;
  const startIndex = Math.max(0, visibleTests - maxVisibleRows);
  const visibleTestSlice = TEST_NAMES.slice(startIndex, visibleTests);

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL_X,
        top: TERMINAL_Y,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        opacity: terminalOpacity,
        borderRadius: WINDOW_BORDER_RADIUS,
        border: `1px solid ${WINDOW_FRAME_COLOR}`,
        backgroundColor: WINDOW_FRAME_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Title Bar */}
      <div
        style={{
          height: TITLE_BAR_HEIGHT,
          backgroundColor: TITLE_BAR_COLOR,
          display: 'flex',
          alignItems: 'center',
          padding: '0 14px',
          gap: 8,
        }}
      >
        {/* Terminal icon */}
        <span style={{ fontSize: 14, opacity: 0.6 }}>{'>'}_</span>
        <span
          style={{
            fontFamily: FONT_MONO,
            fontSize: 12,
            color: '#94A3B8',
          }}
        >
          Terminal
        </span>
      </div>

      {/* Terminal Content */}
      <div
        style={{
          padding: '10px 16px',
          display: 'flex',
          flexDirection: 'column',
          gap: 1,
        }}
      >
        {/* Command line */}
        <div
          style={{
            fontFamily: FONT_MONO,
            fontSize: 13,
            color: GREEN_ACCENT,
            marginBottom: 8,
          }}
        >
          {displayedCommand}
          {frame < TERMINAL_FADE_START + 25 && (
            <span
              style={{
                opacity: Math.sin(frame * 0.3) > 0 ? 1 : 0,
                color: '#94A3B8',
              }}
            >
              |
            </span>
          )}
        </div>

        {/* Test results */}
        {visibleTestSlice.map((testName, i) => (
          <div
            key={`${startIndex + i}`}
            style={{
              fontFamily: FONT_MONO,
              fontSize: 12,
              color: GREEN_ACCENT,
              opacity: 0.8,
              lineHeight: '22px',
            }}
          >
            <span style={{ color: GREEN_ACCENT, marginRight: 6 }}>✓</span>
            {testName}
          </div>
        ))}

        {/* Summary */}
        {summaryOpacity > 0 && (
          <div
            style={{
              fontFamily: FONT_MONO,
              fontSize: 14,
              fontWeight: 700,
              color: GREEN_ACCENT,
              opacity: summaryOpacity,
              marginTop: 12,
              paddingTop: 8,
              borderTop: `2px solid rgba(90, 170, 110, 0.3)`,
            }}
          >
            {TEST_COUNT} tests passing
          </div>
        )}
      </div>
    </div>
  );
};

// ─── Comparison Label ────────────────────────────────────────────
const ComparisonLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_START + LABEL_FADE_DURATION],
    [0, 0.78],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 1020,
        top: 380,
        width: 400,
        opacity,
        textAlign: 'center',
      }}
    >
      <div
        style={{
          fontFamily: FONT_SANS,
          fontSize: 15,
          color: BLUE_ACCENT,
          lineHeight: '24px',
        }}
      >
        With tests: prompt specifies only intent
      </div>
    </div>
  );
};

// ─── Main Component ──────────────────────────────────────────────
export const Part4PrecisionTradeoff05MinimalPromptWithTests: React.FC = () => {
  const frame = useCurrentFrame();

  // Global fade-out
  const fadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: fadeOut,
      }}
    >
      {/* Prompt editor — visible from frame 0 */}
      <EditorWindow />

      {/* Terminal window — appears at frame 60 */}
      <TerminalWindow />

      {/* Test wall lines — draw from frame 120 */}
      <Sequence from={WALLS_START} layout="none">
        <TestWalls />
      </Sequence>

      {/* Comparison label */}
      <ComparisonLabel />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff05MinimalPromptWithTests;
