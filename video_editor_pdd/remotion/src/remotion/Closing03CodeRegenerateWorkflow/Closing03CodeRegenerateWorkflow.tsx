import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BG_COLOR,
  SANS_FONT,
  TEXT_DEFAULT,
  ANNOTATION_UNDERLINE,
  ANNOTATION_START,
  ANNOTATION_DURATION,
} from './constants';
import CodePanel from './CodePanel';
import TestPanel from './TestPanel';
import TerminalStrip from './TerminalStrip';

export const defaultClosing03CodeRegenerateWorkflowProps = {};

export const Closing03CodeRegenerateWorkflow: React.FC = () => {
  const frame = useCurrentFrame();

  // Annotation fade-in
  const annotationOpacity =
    frame >= ANNOTATION_START
      ? interpolate(
          frame,
          [ANNOTATION_START, ANNOTATION_START + ANNOTATION_DURATION],
          [0, 0.78],
          {
            easing: Easing.out(Easing.quad),
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }
        )
      : 0;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Code block — left zone */}
      <CodePanel />

      {/* Test panel — right zone */}
      <TestPanel />

      {/* Terminal strip — bottom zone */}
      <TerminalStrip />

      {/* Annotation: "Never opened the file." */}
      {annotationOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            left: 60,
            top: 760,
            width: 860,
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
            opacity: annotationOpacity,
          }}
        >
          <span
            style={{
              fontFamily: SANS_FONT,
              fontSize: 18,
              fontStyle: 'italic',
              color: TEXT_DEFAULT,
              letterSpacing: 0.3,
            }}
          >
            Never opened the file.
          </span>
          <div
            style={{
              width: 200,
              height: 2,
              backgroundColor: ANNOTATION_UNDERLINE,
              opacity: 0.7,
              marginTop: 6,
              borderRadius: 1,
            }}
          />
        </div>
      )}
    </AbsoluteFill>
  );
};

export default Closing03CodeRegenerateWorkflow;
