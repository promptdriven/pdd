import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  HEADER_COLOR,
  MONO_FONT,
  TEST_PANEL_X,
  TEST_PANEL_Y,
  TEST_PANEL_W,
  TEST_PANEL_H,
  EXISTING_TESTS,
  NEW_TEST,
  TEST_GREEN,
  BUG_RED,
  PASS_GREEN,
  TEXT_DEFAULT,
  LAYOUT_FADEIN_END,
  NEW_TEST_APPEAR,
  TESTS_PASS_FRAME,
} from './constants';

const TestPanel: React.FC = () => {
  const frame = useCurrentFrame();

  const layoutOpacity = interpolate(frame, [0, LAYOUT_FADEIN_END], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
  });

  // New test fade-in
  const newTestOpacity = interpolate(
    frame,
    [NEW_TEST_APPEAR, NEW_TEST_APPEAR + 12],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Test status flip (fail -> pass) at TESTS_PASS_FRAME
  const flipProgress = interpolate(
    frame,
    [TESTS_PASS_FRAME, TESTS_PASS_FRAME + 10],
    [0, 1],
    {
      easing: Easing.out(Easing.back(1.6)),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const newTestPassing = frame >= TESTS_PASS_FRAME;

  // Green pulse effect
  const pulseOpacity =
    frame >= TESTS_PASS_FRAME && frame < TESTS_PASS_FRAME + 15
      ? interpolate(
          frame,
          [TESTS_PASS_FRAME, TESTS_PASS_FRAME + 7, TESTS_PASS_FRAME + 15],
          [0, 0.12, 0],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        )
      : 0;

  const lineHeight = 38;
  const startY = 55;
  const startX = 24;

  return (
    <div
      style={{
        position: 'absolute',
        left: TEST_PANEL_X,
        top: TEST_PANEL_Y,
        width: TEST_PANEL_W,
        height: TEST_PANEL_H,
        backgroundColor: `rgba(30, 41, 59, 0.3)`,
        borderRadius: 8,
        opacity: layoutOpacity,
        overflow: 'hidden',
      }}
    >
      {/* Header */}
      <div
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: 8,
          padding: '10px 16px',
          borderBottom: '1px solid rgba(100, 116, 139, 0.15)',
        }}
      >
        <span
          style={{
            fontFamily: MONO_FONT,
            fontSize: 11,
            color: HEADER_COLOR,
            opacity: 0.8,
          }}
        >
          test_user_parser.py
        </span>
      </div>

      {/* Green pulse overlay */}
      {pulseOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            inset: 0,
            backgroundColor: PASS_GREEN,
            opacity: pulseOpacity,
            borderRadius: 8,
            pointerEvents: 'none',
          }}
        />
      )}

      {/* Existing tests */}
      {EXISTING_TESTS.map((testName, i) => (
        <div
          key={testName}
          style={{
            position: 'absolute',
            top: startY + i * lineHeight,
            left: startX,
            display: 'flex',
            alignItems: 'center',
            gap: 10,
          }}
        >
          <span
            style={{
              fontFamily: MONO_FONT,
              fontSize: 14,
              color: TEST_GREEN,
              opacity: 0.8,
            }}
          >
            ✓
          </span>
          <span
            style={{
              fontFamily: MONO_FONT,
              fontSize: 12,
              color: TEXT_DEFAULT,
              opacity: 0.7,
            }}
          >
            {testName}
          </span>
        </div>
      ))}

      {/* New test line */}
      {frame >= NEW_TEST_APPEAR && (
        <div
          style={{
            position: 'absolute',
            top: startY + EXISTING_TESTS.length * lineHeight,
            left: 0,
            right: 0,
            height: lineHeight,
            display: 'flex',
            alignItems: 'center',
            paddingLeft: startX,
            gap: 10,
            backgroundColor: `rgba(217, 148, 74, 0.08)`,
            opacity: newTestOpacity,
          }}
        >
          {/* Status icon with flip animation */}
          <span
            style={{
              fontFamily: MONO_FONT,
              fontSize: 14,
              color: newTestPassing ? PASS_GREEN : BUG_RED,
              opacity: 0.9,
              display: 'inline-block',
              transform: `scale(${
                newTestPassing
                  ? interpolate(
                      flipProgress,
                      [0, 0.5, 1],
                      [1, 1.3, 1],
                      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
                    )
                  : 1
              })`,
            }}
          >
            {newTestPassing ? '✓' : '✗'}
          </span>
          <span
            style={{
              fontFamily: MONO_FONT,
              fontSize: 12,
              color: TEXT_DEFAULT,
              opacity: 0.7,
            }}
          >
            {NEW_TEST}
          </span>
        </div>
      )}
    </div>
  );
};

export default TestPanel;
