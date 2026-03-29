import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface TestRowData {
  name: string;
  status: 'pass';
}

interface TestSuitePanelProps {
  tests: TestRowData[];
  headerColor: string;
  checkColor: string;
  textColor: string;
  panelBg: string;
  x: number;
  y: number;
  width: number;
  padding: number;
  borderRadius: number;
  fadeStartFrame: number;
  fadeDuration: number;
  rowStagger: number;
  morphProgress: number;
}

const TestSuitePanel: React.FC<TestSuitePanelProps> = ({
  tests,
  headerColor,
  checkColor,
  textColor,
  panelBg,
  x,
  y,
  width,
  padding,
  borderRadius,
  fadeStartFrame,
  fadeDuration,
  rowStagger,
  morphProgress,
}) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - fadeStartFrame;

  // Panel fade-in
  const panelOpacity = interpolate(
    relativeFrame,
    [0, fadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Slide from right
  const slideX = interpolate(
    relativeFrame,
    [0, fadeDuration],
    [40, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Header appearance
  const headerOpacity = interpolate(
    relativeFrame,
    [5, 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Morph effect: subtle scale pulse
  const morphScale = interpolate(
    morphProgress,
    [0, 0.5, 1],
    [1, 1.02, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  if (relativeFrame < 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: x + slideX,
        top: y,
        width,
        opacity: panelOpacity,
        transform: `scale(${morphScale})`,
        transformOrigin: 'center center',
      }}
    >
      {/* Panel */}
      <div
        style={{
          position: 'relative',
          background: panelBg,
          borderRadius,
          padding,
        }}
      >
        {/* Header */}
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 12,
            fontWeight: 700,
            color: headerColor,
            letterSpacing: 3,
            marginBottom: 16,
            opacity: headerOpacity,
          }}
        >
          TEST SUITE
        </div>

        {/* Test rows */}
        {tests.map((test, i) => {
          const rowStart = fadeDuration + i * rowStagger;
          const rowProgress = interpolate(
            relativeFrame,
            [rowStart, rowStart + 15],
            [0, 1],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );

          // Bounce effect for checkmark (easeOut with back overshoot)
          const checkScale = interpolate(
            relativeFrame,
            [rowStart, rowStart + 8, rowStart + 15],
            [0, 1.3, 1],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
          );

          return (
            <div
              key={test.name}
              style={{
                display: 'flex',
                alignItems: 'center',
                gap: 12,
                padding: '8px 0',
                opacity: rowProgress,
                borderBottom:
                  i < tests.length - 1
                    ? '1px solid rgba(255,255,255,0.06)'
                    : 'none',
              }}
            >
              {/* Checkmark */}
              <div
                style={{
                  width: 20,
                  height: 20,
                  flexShrink: 0,
                  display: 'flex',
                  alignItems: 'center',
                  justifyContent: 'center',
                  transform: `scale(${checkScale})`,
                }}
              >
                <svg width={20} height={20} viewBox="0 0 20 20">
                  <circle cx={10} cy={10} r={9} fill="none" stroke={checkColor} strokeWidth={1.5} opacity={0.3} />
                  <path
                    d="M6 10.5 L9 13.5 L14 7"
                    fill="none"
                    stroke={checkColor}
                    strokeWidth={2}
                    strokeLinecap="round"
                    strokeLinejoin="round"
                  />
                </svg>
              </div>

              {/* Test name */}
              <span
                style={{
                  fontFamily: '"JetBrains Mono", monospace',
                  fontSize: 14,
                  color: textColor,
                  flex: 1,
                }}
              >
                {test.name}
              </span>

              {/* PASS label */}
              <span
                style={{
                  fontFamily: '"JetBrains Mono", monospace',
                  fontSize: 12,
                  fontWeight: 700,
                  color: checkColor,
                }}
              >
                PASS
              </span>
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default TestSuitePanel;
