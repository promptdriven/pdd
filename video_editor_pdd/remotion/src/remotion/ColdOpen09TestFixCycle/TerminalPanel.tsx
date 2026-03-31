import React from 'react';
import { useCurrentFrame, interpolate, Easing, spring } from 'remotion';
import {
  TERMINAL_BG,
  TEXT_PRIMARY,
  TEXT_MUTED,
  COLOR_RED,
  COLOR_GREEN,
  COLOR_SURFACE0,
  CODE_FONT,
  TERMINAL_FONT_SIZE,
  SUMMARY_FONT_SIZE,
  ERROR_FONT_SIZE,
  TERMINAL_LINE_HEIGHT,
  PANEL_BORDER_RADIUS,
  TITLE_BAR_HEIGHT,
  PANEL_PADDING_X,
  PANEL_PADDING_Y,
  PYTEST_COMMAND,
  PDD_COMMAND,
  FAILING_TEST,
  ERROR_TRACE_LINES,
  TEST_RESULTS,
  FPS,
  PHASE_FIRST_RUN_START,
  PHASE_FAILURE_START,
  PHASE_FAILURE_END,
  PHASE_FIX_CMD_START,
  PHASE_SECOND_RUN_START,
  PHASE_RESULTS_START,
  PHASE_SUMMARY_START,
  PHASE_SUMMARY_END,
} from './constants';

interface TerminalPanelProps {
  width: number;
  height: number;
}

/** Helper to type out text character by character. */
function getTypedText(
  text: string,
  frame: number,
  startFrame: number,
  typingFrames: number
): string {
  const rel = frame - startFrame;
  if (rel < 0) return '';
  const count = Math.floor(
    interpolate(rel, [0, typingFrames], [0, text.length], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    })
  );
  return text.slice(0, count);
}

export const TerminalPanel: React.FC<TerminalPanelProps> = ({
  width,
  height,
}) => {
  const frame = useCurrentFrame();

  // --- Cursor blink ---
  const cursorBlink = Math.floor(frame / 8) % 2 === 0;

  // --- Phase helpers ---
  const showFirstRun = frame >= PHASE_FIRST_RUN_START;
  const showFailure = frame >= PHASE_FAILURE_START;
  const showFixCmd = frame >= PHASE_FIX_CMD_START;
  const showSecondRun = frame >= PHASE_SECOND_RUN_START;
  const showResults = frame >= PHASE_RESULTS_START;
  const showSummary = frame >= PHASE_SUMMARY_START;

  // --- Typed commands ---
  const firstCmdText = showFirstRun
    ? getTypedText(PYTEST_COMMAND, frame, PHASE_FIRST_RUN_START, 20)
    : '';
  const fixCmdText = showFixCmd
    ? getTypedText(PDD_COMMAND, frame, PHASE_FIX_CMD_START, 20)
    : '';
  const secondCmdText = showSecondRun
    ? getTypedText(PYTEST_COMMAND, frame, PHASE_SECOND_RUN_START, 20)
    : '';

  // --- Failure appearance ---
  const failureOpacity =
    showFailure && frame < PHASE_FIX_CMD_START
      ? interpolate(
          frame,
          [PHASE_FAILURE_START, PHASE_FAILURE_START + 10],
          [0, 1],
          {
            easing: Easing.out(Easing.quad),
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }
        )
      : showFailure && frame < PHASE_SECOND_RUN_START
        ? 1
        : 0;

  // --- Test results, one by one with spring ---
  const testResultsVisible: Array<{ name: string; opacity: number; scale: number }> =
    TEST_RESULTS.map((name, i) => {
      const testFrame = PHASE_RESULTS_START + i * 18;
      if (frame < testFrame) return { name, opacity: 0, scale: 0.5 };

      const s = spring({
        frame: frame - testFrame,
        fps: FPS,
        config: { damping: 12, stiffness: 200, mass: 0.5 },
      });

      return { name, opacity: s, scale: 0.8 + 0.2 * s };
    });

  // --- Summary glow ---
  const summaryOpacity = showSummary
    ? interpolate(
        frame,
        [PHASE_SUMMARY_START, PHASE_SUMMARY_START + 10],
        [0, 1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : 0;

  // Summary glow pulse
  const glowIntensity = showSummary
    ? interpolate(
        (frame - PHASE_SUMMARY_START) % 40,
        [0, 20, 40],
        [0.3, 0.6, 0.3],
        {
          easing: Easing.inOut(Easing.sin),
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        }
      )
    : 0;

  return (
    <div
      style={{
        width,
        height,
        backgroundColor: TERMINAL_BG,
        borderRadius: PANEL_BORDER_RADIUS,
        overflow: 'hidden',
        display: 'flex',
        flexDirection: 'column',
        position: 'relative',
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: TITLE_BAR_HEIGHT,
          backgroundColor: COLOR_SURFACE0,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 14,
          paddingRight: 14,
          gap: 8,
          flexShrink: 0,
        }}
      >
        <div style={{ display: 'flex', gap: 6 }}>
          {['#F38BA8', '#F9E2AF', '#A6E3A1'].map((dotColor, i) => (
            <div
              key={i}
              style={{
                width: 10,
                height: 10,
                borderRadius: '50%',
                backgroundColor: dotColor,
                opacity: 0.8,
              }}
            />
          ))}
        </div>
        <span
          style={{
            fontFamily: CODE_FONT,
            fontSize: 12,
            color: TEXT_MUTED,
            marginLeft: 8,
            opacity: 0.85,
          }}
        >
          pytest
        </span>
      </div>

      {/* Terminal content */}
      <div
        style={{
          flex: 1,
          padding: `${PANEL_PADDING_Y}px ${PANEL_PADDING_X}px`,
          overflow: 'hidden',
          fontFamily: CODE_FONT,
          fontSize: TERMINAL_FONT_SIZE,
          lineHeight: TERMINAL_LINE_HEIGHT,
          position: 'relative',
        }}
      >
        {/* Blinking cursor before first command */}
        {!showFirstRun && (
          <span style={{ color: TEXT_MUTED, opacity: cursorBlink ? 0.8 : 0 }}>
            $ _
          </span>
        )}

        {/* First command: pytest */}
        {showFirstRun && (
          <div style={{ whiteSpace: 'pre', marginBottom: 4 }}>
            <span style={{ color: TEXT_MUTED, opacity: 0.78 }}>$ </span>
            <span style={{ color: TEXT_PRIMARY }}>{firstCmdText}</span>
            {frame < PHASE_FIRST_RUN_START + 25 && (
              <span style={{ color: TEXT_PRIMARY, opacity: cursorBlink ? 1 : 0 }}>
                _
              </span>
            )}
          </div>
        )}

        {/* Failure block */}
        {failureOpacity > 0 && (
          <div style={{ opacity: failureOpacity, marginTop: 8 }}>
            {/* FAIL line */}
            <div style={{ whiteSpace: 'pre' }}>
              <span style={{ color: COLOR_RED, fontWeight: 'bold' }}>
                FAIL{' '}
              </span>
              <span style={{ color: TEXT_PRIMARY }}>
                test_email_validator.py::
              </span>
              <span style={{ color: TEXT_PRIMARY }}>{FAILING_TEST}</span>
              <span style={{ color: COLOR_RED, marginLeft: 8 }}> ✗</span>
            </div>

            {/* Error trace */}
            <div style={{ marginTop: 6, marginLeft: 8 }}>
              {ERROR_TRACE_LINES.map((line, i) => (
                <div
                  key={i}
                  style={{
                    fontSize: ERROR_FONT_SIZE,
                    color: COLOR_RED,
                    opacity: 0.7,
                    whiteSpace: 'pre',
                    lineHeight: 1.6,
                  }}
                >
                  {line}
                </div>
              ))}
            </div>

            {/* Short summary */}
            <div style={{ marginTop: 8, whiteSpace: 'pre' }}>
              <span style={{ color: COLOR_RED, fontWeight: 'bold' }}>
                1 failed
              </span>
              <span style={{ color: TEXT_MUTED }}>, 4 passed</span>
            </div>
          </div>
        )}

        {/* Fix command */}
        {showFixCmd && frame < PHASE_SECOND_RUN_START && (
          <div style={{ whiteSpace: 'pre', marginTop: 12 }}>
            <span style={{ color: TEXT_MUTED, opacity: 0.78 }}>$ </span>
            <span style={{ color: TEXT_PRIMARY }}>{fixCmdText}</span>
            {frame < PHASE_FIX_CMD_START + 25 && (
              <span style={{ color: TEXT_PRIMARY, opacity: cursorBlink ? 1 : 0 }}>
                _
              </span>
            )}
            {frame >= PHASE_FIX_CMD_START + 25 && (
              <div style={{ color: TEXT_MUTED, marginTop: 4, fontSize: ERROR_FONT_SIZE }}>
                Regenerating email_validator.py...
              </div>
            )}
          </div>
        )}

        {/* Second command: pytest (re-run) */}
        {showSecondRun && (
          <div style={{ whiteSpace: 'pre', marginTop: 12 }}>
            <span style={{ color: TEXT_MUTED, opacity: 0.78 }}>$ </span>
            <span style={{ color: TEXT_PRIMARY }}>{secondCmdText}</span>
            {frame < PHASE_SECOND_RUN_START + 25 && (
              <span style={{ color: TEXT_PRIMARY, opacity: cursorBlink ? 1 : 0 }}>
                _
              </span>
            )}
          </div>
        )}

        {/* Test results - green checkmarks */}
        {showResults && (
          <div style={{ marginTop: 8 }}>
            {testResultsVisible.map((test, i) => {
              if (test.opacity <= 0) return null;
              return (
                <div
                  key={i}
                  style={{
                    whiteSpace: 'pre',
                    opacity: test.opacity,
                    transform: `scale(${test.scale})`,
                    transformOrigin: 'left center',
                    lineHeight: 1.8,
                  }}
                >
                  <span style={{ color: COLOR_GREEN, fontWeight: 'bold' }}>
                    {'  '}✓{' '}
                  </span>
                  <span style={{ color: TEXT_PRIMARY }}>{test.name}</span>
                </div>
              );
            })}
          </div>
        )}

        {/* Summary line */}
        {summaryOpacity > 0 && (
          <div
            style={{
              marginTop: 12,
              opacity: summaryOpacity,
              whiteSpace: 'pre',
              position: 'relative',
            }}
          >
            <span
              style={{
                fontSize: SUMMARY_FONT_SIZE,
                fontWeight: 'bold',
                color: COLOR_GREEN,
                textShadow: `0 0 ${8 + glowIntensity * 16}px ${COLOR_GREEN}`,
              }}
            >
              5 passed ✓
            </span>
          </div>
        )}
      </div>
    </div>
  );
};

export default TerminalPanel;
