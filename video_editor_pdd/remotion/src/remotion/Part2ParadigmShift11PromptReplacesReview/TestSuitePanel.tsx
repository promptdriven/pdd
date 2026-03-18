import React from 'react';
import { useCurrentFrame, interpolate, Easing, spring, useVideoConfig } from 'remotion';
import { COLORS, TEST_ITEMS } from './constants';

export const TestSuitePanel: React.FC<{
  appearStart: number;
  checkInterval: number;
}> = ({ appearStart, checkInterval }) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const panelOpacity = interpolate(
    frame,
    [appearStart, appearStart + 15],
    [0, 1],
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
        left: 280,
        top: 525,
        width: 400,
        height: 250,
        backgroundColor: 'rgba(30, 41, 59, 0.2)',
        borderRadius: 4,
        opacity: panelOpacity,
        overflow: 'hidden',
      }}
    >
      {/* Header */}
      <div
        style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 10,
          color: COLORS.green,
          opacity: 0.4,
          padding: '8px 12px 4px',
          borderBottom: '1px solid rgba(30, 41, 59, 0.3)',
        }}
      >
        test_suite.py
      </div>

      {/* Test items */}
      <div style={{ padding: '8px 12px' }}>
        {TEST_ITEMS.map((test, i) => {
          const checkFrame = appearStart + i * checkInterval;
          const isVisible = frame >= checkFrame;

          // Use spring for the checkmark pop with back easing feel
          const checkScale = isVisible
            ? spring({
                frame: frame - checkFrame,
                fps,
                config: {
                  damping: 12,
                  stiffness: 200,
                  mass: 0.5,
                },
              })
            : 0;

          const textOpacity = isVisible
            ? interpolate(
                frame,
                [checkFrame, checkFrame + 8],
                [0, 0.5],
                {
                  extrapolateLeft: 'clamp',
                  extrapolateRight: 'clamp',
                }
              )
            : 0;

          return (
            <div
              key={i}
              style={{
                display: 'flex',
                alignItems: 'center',
                gap: 8,
                fontFamily: 'JetBrains Mono, monospace',
                fontSize: 11,
                lineHeight: '22px',
                color: COLORS.green,
                opacity: textOpacity,
              }}
            >
              <span
                style={{
                  display: 'inline-block',
                  transform: `scale(${checkScale})`,
                  color: COLORS.green,
                  fontWeight: 700,
                  fontSize: 14,
                  width: 16,
                  textAlign: 'center',
                }}
              >
                {'\u2713'}
              </span>
              <span>{test}</span>
            </div>
          );
        })}
      </div>
    </div>
  );
};
