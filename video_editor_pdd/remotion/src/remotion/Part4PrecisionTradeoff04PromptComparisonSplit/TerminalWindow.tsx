import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { MONO_FONT, SANS_FONT, COLORS } from './constants';

const TerminalWindow: React.FC<{
  x: number;
  y: number;
  width: number;
  height: number;
  command: string;
  testResults: string[];
  startFrame: number;
  scrollSpeed: number;
}> = ({
  x,
  y,
  width,
  height,
  command,
  testResults,
  startFrame,
  scrollSpeed,
}) => {
  const frame = useCurrentFrame();
  const elapsed = Math.max(0, frame - startFrame);

  // Terminal window open animation
  const openProgress = interpolate(elapsed, [0, 15], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Command appears after terminal opens
  const commandOpacity = interpolate(elapsed, [10, 18], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Test results scroll
  const testStartElapsed = 20;
  const testsElapsed = Math.max(0, elapsed - testStartElapsed);
  const revealedTests = Math.min(
    testResults.length,
    Math.floor(testsElapsed * scrollSpeed)
  );

  // Summary line
  const allTestsDone =
    elapsed >= testStartElapsed + testResults.length / scrollSpeed;
  const summaryElapsed = Math.max(
    0,
    elapsed - (testStartElapsed + testResults.length / scrollSpeed + 10)
  );
  const summaryOpacity = interpolate(summaryElapsed, [0, 10], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Scroll offset for tests (scroll up as more appear)
  const testLineHeight = 14;
  const testAreaHeight = height - 60; // minus header and summary
  const maxVisibleTests = Math.floor(testAreaHeight / testLineHeight);
  const scrollOffset = Math.max(0, revealedTests - maxVisibleTests);

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height: height * openProgress,
        backgroundColor: COLORS.terminalBg,
        borderRadius: 4,
        border: '1px solid rgba(51, 65, 85, 0.3)',
        overflow: 'hidden',
        opacity: openProgress,
      }}
    >
      {/* Terminal header */}
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
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#EF4444',
            opacity: 0.6,
          }}
        />
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#F59E0B',
            opacity: 0.6,
          }}
        />
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#22C55E',
            opacity: 0.6,
          }}
        />
        <span
          style={{
            fontFamily: MONO_FONT,
            fontSize: 10,
            color: COLORS.commandColor,
            marginLeft: 8,
            opacity: 0.5,
          }}
        >
          terminal
        </span>
      </div>

      {/* Command line */}
      <div
        style={{
          padding: '6px 10px',
          opacity: commandOpacity,
        }}
      >
        <span
          style={{
            fontFamily: MONO_FONT,
            fontSize: 11,
            color: '#5AAA6E',
            opacity: 0.7,
          }}
        >
          ${' '}
        </span>
        <span
          style={{
            fontFamily: MONO_FONT,
            fontSize: 11,
            color: COLORS.commandColor,
          }}
        >
          {command}
        </span>
      </div>

      {/* Test results */}
      <div
        style={{
          padding: '0 10px',
          height: testAreaHeight,
          overflow: 'hidden',
          position: 'relative',
        }}
      >
        <div
          style={{
            transform: `translateY(-${scrollOffset * testLineHeight}px)`,
          }}
        >
          {testResults.slice(0, revealedTests).map((test, i) => (
            <div
              key={i}
              style={{
                height: testLineHeight,
                display: 'flex',
                alignItems: 'center',
                gap: 6,
              }}
            >
              <span
                style={{
                  fontFamily: MONO_FONT,
                  fontSize: 9,
                  color: COLORS.testColor,
                  opacity: 0.7,
                }}
              >
                ✓
              </span>
              <span
                style={{
                  fontFamily: MONO_FONT,
                  fontSize: 9,
                  color: COLORS.testColor,
                  opacity: 0.7,
                }}
              >
                {test}
              </span>
            </div>
          ))}
        </div>
      </div>

      {/* Summary line */}
      {allTestsDone && (
        <div
          style={{
            position: 'absolute',
            bottom: 8,
            left: 0,
            right: 0,
            textAlign: 'center',
            opacity: summaryOpacity,
          }}
        >
          <span
            style={{
              fontFamily: SANS_FONT,
              fontSize: 12,
              fontWeight: 700,
              color: COLORS.testColor,
            }}
          >
            47 passed ✓
          </span>
        </div>
      )}
    </div>
  );
};

export default TerminalWindow;
