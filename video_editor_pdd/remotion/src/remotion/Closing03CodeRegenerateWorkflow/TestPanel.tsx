import React from 'react';
import { useCurrentFrame, interpolate, Easing, spring, useVideoConfig } from 'remotion';
import { COLORS, FONTS, LAYOUT, EXISTING_TESTS, NEW_TEST } from './constants';

const LINE_HEIGHT = 28;

const TestLine: React.FC<{
  name: string;
  status: 'pass' | 'fail';
  highlight?: boolean;
}> = ({ name, status, highlight }) => {
  const isPass = status === 'pass';
  return (
    <div
      style={{
        display: 'flex',
        alignItems: 'center',
        gap: 10,
        height: LINE_HEIGHT,
        padding: '0 12px',
        fontFamily: FONTS.mono,
        fontSize: 12,
        ...(highlight
          ? { backgroundColor: `rgba(217, 148, 74, 0.08)` }
          : {}),
      }}
    >
      <span
        style={{
          color: isPass ? COLORS.greenCheck : COLORS.red,
          fontSize: 14,
          width: 16,
          textAlign: 'center',
        }}
      >
        {isPass ? '✓' : '✗'}
      </span>
      <span style={{ color: COLORS.textDefault, opacity: 0.7 }}>{name}</span>
    </div>
  );
};

export const TestPanel: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const { x, y, width, height } = LAYOUT.testPanel;

  // Layout fade-in
  const panelOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // New test appears at frame 50
  const newTestOpacity = interpolate(frame, [50, 62], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // At frame 160, the new test flips from fail to pass
  const newTestPasses = frame >= 160;

  // Spring bounce for the check flip
  const flipScale = newTestPasses
    ? spring({
        frame: frame - 160,
        fps,
        config: {
          damping: 12,
          stiffness: 200,
          mass: 0.5,
        },
      })
    : 1;

  // Green pulse at frame 160
  const pulseOpacity =
    frame >= 160 && frame < 175
      ? interpolate(frame, [160, 167, 175], [0, 0.15, 0], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        })
      : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
        backgroundColor: `rgba(30, 41, 59, 0.3)`,
        borderRadius: 8,
        opacity: panelOpacity,
        overflow: 'hidden',
      }}
    >
      {/* Header */}
      <div
        style={{
          padding: '10px 16px',
          borderBottom: '1px solid rgba(100, 116, 139, 0.15)',
        }}
      >
        <span
          style={{
            fontFamily: FONTS.mono,
            fontSize: 11,
            color: COLORS.textDim,
            opacity: 0.5,
          }}
        >
          test_user_parser.py
        </span>
      </div>

      {/* Test list */}
      <div style={{ padding: '12px 8px' }}>
        {EXISTING_TESTS.map((test, i) => (
          <TestLine key={i} name={test} status="pass" />
        ))}

        {/* New test line */}
        {frame >= 50 && (
          <div style={{ opacity: newTestOpacity }}>
            <div
              style={{
                display: 'flex',
                alignItems: 'center',
                gap: 10,
                height: LINE_HEIGHT,
                padding: '0 12px',
                fontFamily: FONTS.mono,
                fontSize: 12,
                backgroundColor: newTestPasses
                  ? 'transparent'
                  : `rgba(217, 148, 74, 0.08)`,
              }}
            >
              <span
                style={{
                  color: newTestPasses ? COLORS.greenCheck : COLORS.red,
                  fontSize: 14,
                  width: 16,
                  textAlign: 'center',
                  display: 'inline-block',
                  transform: `scale(${flipScale})`,
                }}
              >
                {newTestPasses ? '✓' : '✗'}
              </span>
              <span style={{ color: COLORS.textDefault, opacity: 0.7 }}>
                {NEW_TEST}
              </span>
            </div>
          </div>
        )}
      </div>

      {/* Green pulse overlay */}
      {pulseOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            inset: 0,
            backgroundColor: COLORS.greenCheck,
            opacity: pulseOpacity,
            borderRadius: 8,
            pointerEvents: 'none',
          }}
        />
      )}
    </div>
  );
};
