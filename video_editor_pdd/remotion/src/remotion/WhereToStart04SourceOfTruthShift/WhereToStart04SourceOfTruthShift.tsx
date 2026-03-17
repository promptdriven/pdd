import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  CANVAS,
  COLORS,
  TIMING,
  LAYOUT,
  AUTH_HANDLER_CODE,
  AUTH_PROMPT_CONTENT,
} from './constants';
import { EditorWindow } from './EditorWindow';
import { DirectionArrow } from './DirectionArrow';
import { TestWalls } from './TestWalls';
import { Terminal } from './Terminal';

export const defaultWhereToStart04SourceOfTruthShiftProps = {};

export const WhereToStart04SourceOfTruthShift: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Label animations ---
  const artifactLabelOpacity = interpolate(
    frame,
    [TIMING.labelsStart, TIMING.labelsStart + TIMING.labelFadeDuration],
    [0, 0.3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const sourceLabelOpacity = interpolate(
    frame,
    [TIMING.labelsStart, TIMING.labelsStart + TIMING.labelFadeDuration],
    [0, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // --- Callout animation ---
  const calloutOpacity = interpolate(
    frame,
    [TIMING.calloutStart, TIMING.calloutStart + TIMING.calloutFadeDuration],
    [0, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.backgroundColor,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* ===== Code Block (left) — desaturating ===== */}
      <EditorWindow
        x={LAYOUT.codeBlock.x}
        y={LAYOUT.codeBlock.y}
        width={LAYOUT.codeBlock.width}
        height={LAYOUT.codeBlock.height}
        filename="auth_handler.py"
        lines={AUTH_HANDLER_CODE}
        isCode
        desaturate
      />

      {/* "artifact" label below code block */}
      <div
        style={{
          position: 'absolute',
          left: LAYOUT.artifactLabel.x,
          top: LAYOUT.artifactLabel.y,
          transform: 'translateX(-50%)',
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          fontStyle: 'italic',
          color: COLORS.artifactLabel,
          opacity: artifactLabelOpacity,
        }}
      >
        artifact
      </div>

      {/* ===== Direction Arrow ===== */}
      <DirectionArrow />

      {/* ===== Prompt Document (right) — glowing ===== */}
      <EditorWindow
        x={LAYOUT.promptDoc.x}
        y={LAYOUT.promptDoc.y}
        width={LAYOUT.promptDoc.width}
        height={LAYOUT.promptDoc.height}
        filename="auth_handler.prompt"
        lines={AUTH_PROMPT_CONTENT}
        isCode={false}
        glow
      />

      {/* "source of truth" label below prompt */}
      <div
        style={{
          position: 'absolute',
          left: LAYOUT.sourceLabel.x,
          top: LAYOUT.sourceLabel.y,
          transform: 'translateX(-50%)',
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          fontWeight: 700,
          color: COLORS.sourceLabel,
          opacity: sourceLabelOpacity,
        }}
      >
        source of truth
      </div>

      {/* ===== Test Wall Icons ===== */}
      <TestWalls />

      {/* ===== Terminal ===== */}
      <Terminal />

      {/* ===== Callout Text ===== */}
      <div
        style={{
          position: 'absolute',
          left: LAYOUT.callout.x,
          top: LAYOUT.callout.y,
          transform: 'translateX(-50%)',
          fontFamily: 'Inter, sans-serif',
          fontSize: 16,
          color: COLORS.calloutText,
          opacity: calloutOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        The prompt is your new{' '}
        <span
          style={{
            color: COLORS.calloutHighlight,
            opacity: 0.8 / 0.6, // relative to parent opacity
            fontWeight: 600,
          }}
        >
          source of truth
        </span>
        .
      </div>
    </AbsoluteFill>
  );
};

export default WhereToStart04SourceOfTruthShift;
