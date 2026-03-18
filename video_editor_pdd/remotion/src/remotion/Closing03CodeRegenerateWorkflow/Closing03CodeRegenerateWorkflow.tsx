import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, FONTS } from './constants';
import { CodePanel } from './CodePanel';
import { TestPanel } from './TestPanel';
import { TerminalStrip } from './TerminalStrip';

export const defaultClosing03CodeRegenerateWorkflowProps = {};

export const Closing03CodeRegenerateWorkflow: React.FC = () => {
  const frame = useCurrentFrame();

  // Annotation fade-in starting at frame 200
  const annotationOpacity = interpolate(frame, [200, 218], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Underline opacity
  const underlineOpacity = interpolate(frame, [200, 218], [0, 0.15], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Code block — left zone */}
      <CodePanel />

      {/* Test panel — right zone */}
      <TestPanel />

      {/* Terminal strip — bottom zone */}
      <TerminalStrip />

      {/* Annotation: "Never opened the file." */}
      {frame >= 200 && (
        <div
          style={{
            position: 'absolute',
            left: 60,
            top: 760,
            width: 860,
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
          }}
        >
          <span
            style={{
              fontFamily: FONTS.sans,
              fontSize: 16,
              fontStyle: 'italic',
              color: COLORS.textDefault,
              opacity: annotationOpacity,
            }}
          >
            Never opened the file.
          </span>
          <div
            style={{
              width: 200,
              height: 1,
              backgroundColor: COLORS.accentBlue,
              opacity: underlineOpacity,
              marginTop: 6,
            }}
          />
        </div>
      )}
    </AbsoluteFill>
  );
};

export default Closing03CodeRegenerateWorkflow;
