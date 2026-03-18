import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TERMINAL_HEIGHT } from './constants';

interface TerminalWindowProps {
  panelX: number;
  panelWidth: number;
  y: number;
  command: string;
  testResults: string[];
  /** Frame at which the terminal opens (relative to component mount) */
  startFrame: number;
  /** Test results per frame */
  scrollSpeed: number;
}

export const TerminalWindow: React.FC<TerminalWindowProps> = ({
  panelX,
  panelWidth,
  y,
  command,
  testResults,
  startFrame,
  scrollSpeed,
}) => {
  const frame = useCurrentFrame();

  // Terminal fade-in
  const terminalOpacity = interpolate(
    frame,
    [startFrame, startFrame + 15],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) },
  );

  if (frame < startFrame) return null;

  const elapsed = frame - startFrame;

  // Command appears first for 10 frames, then results scroll
  const commandVisible = elapsed >= 0;
  const resultsElapsed = Math.max(0, elapsed - 10);
  const revealedTests = Math.min(
    testResults.length,
    Math.floor(resultsElapsed * scrollSpeed),
  );

  // "47 passed" line appears after all tests
  const allTestsRevealed = revealedTests >= testResults.length;
  const passedLineFrame = startFrame + 10 + Math.ceil(testResults.length / scrollSpeed) + 10;
  const passedOpacity = interpolate(
    frame,
    [passedLineFrame, passedLineFrame + 15],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Calculate scroll offset to keep the latest tests visible
  const testLineHeight = 14;
  const maxVisibleTests = Math.floor((TERMINAL_HEIGHT - 60) / testLineHeight);
  const scrollOffset = Math.max(0, revealedTests - maxVisibleTests);

  return (
    <div
      style={{
        position: 'absolute',
        left: panelX + 10,
        top: y,
        width: panelWidth - 20,
        height: TERMINAL_HEIGHT,
        backgroundColor: COLORS.terminalBg,
        borderRadius: 6,
        border: '1px solid rgba(51, 65, 85, 0.3)',
        overflow: 'hidden',
        opacity: terminalOpacity,
      }}
    >
      {/* Terminal title bar */}
      <div
        style={{
          height: 28,
          backgroundColor: 'rgba(30, 41, 59, 0.8)',
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 10,
          gap: 6,
        }}
      >
        <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#EF4444', opacity: 0.6 }} />
        <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#F59E0B', opacity: 0.6 }} />
        <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#22C55E', opacity: 0.6 }} />
        <span
          style={{
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 10,
            color: COLORS.terminalCommandColor,
            marginLeft: 8,
            opacity: 0.6,
          }}
        >
          terminal
        </span>
      </div>

      {/* Terminal content */}
      <div style={{ padding: '8px 12px', overflow: 'hidden', height: TERMINAL_HEIGHT - 28 }}>
        {/* Command line */}
        {commandVisible && (
          <div
            style={{
              fontFamily: '"JetBrains Mono", monospace',
              fontSize: 11,
              color: COLORS.terminalCommandColor,
              marginBottom: 6,
            }}
          >
            <span style={{ color: COLORS.rightAccent, opacity: 0.7 }}>$</span>{' '}
            {command}
          </div>
        )}

        {/* Scrolling test results */}
        <div style={{ overflow: 'hidden', height: TERMINAL_HEIGHT - 70 }}>
          <div
            style={{
              transform: `translateY(${-scrollOffset * testLineHeight}px)`,
            }}
          >
            {testResults.map((test, i) => {
              if (i >= revealedTests) return null;
              return (
                <div
                  key={i}
                  style={{
                    fontFamily: '"JetBrains Mono", monospace',
                    fontSize: 9,
                    color: COLORS.testCheckColor,
                    opacity: 0.7,
                    height: testLineHeight,
                    display: 'flex',
                    alignItems: 'center',
                    whiteSpace: 'nowrap',
                  }}
                >
                  <span style={{ marginRight: 6, fontSize: 10 }}>✓</span>
                  {test}
                </div>
              );
            })}
          </div>
        </div>

        {/* Summary line */}
        {allTestsRevealed && (
          <div
            style={{
              position: 'absolute',
              bottom: 8,
              left: 12,
              right: 12,
              fontFamily: 'Inter, sans-serif',
              fontSize: 12,
              fontWeight: 700,
              color: COLORS.rightAccent,
              textAlign: 'center',
              opacity: passedOpacity,
              backgroundColor: COLORS.terminalBg,
              paddingTop: 4,
            }}
          >
            {testResults.length} passed ✓
          </div>
        )}
      </div>
    </div>
  );
};
