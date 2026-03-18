import React from 'react';
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from 'remotion';
import {
  CANVAS,
  COLORS,
  CODE_BLOCK,
  PROMPT_BLOCK,
  ARROW,
  TIMING,
  AUTH_HANDLER_CODE,
  PROMPT_CONTENT,
} from './constants';
import EditorWindow from './EditorWindow';
import DirectionArrow from './DirectionArrow';
import TestWalls from './TestWalls';
import TerminalBlock from './TerminalBlock';

export const defaultWhereToStart04SourceOfTruthShiftProps = {};

export const WhereToStart04SourceOfTruthShift: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Labels ---
  const artifactLabelOpacity = interpolate(
    frame,
    [TIMING.labelsStart, TIMING.labelsStart + TIMING.labelDuration],
    [0, 0.3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const sourceLabelOpacity = interpolate(
    frame,
    [TIMING.labelsStart, TIMING.labelsStart + TIMING.labelDuration],
    [0, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // --- Callout ---
  const calloutOpacity = interpolate(
    frame,
    [TIMING.calloutStart, TIMING.calloutStart + TIMING.calloutDuration],
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
        fontFamily: '"Inter", sans-serif',
      }}
    >
      {/* Code block (left) — desaturates from 0.5 to 0.2 */}
      <EditorWindow
        x={CODE_BLOCK.x}
        y={CODE_BLOCK.y}
        width={CODE_BLOCK.width}
        height={CODE_BLOCK.height}
        filename={CODE_BLOCK.filename}
        lines={AUTH_HANDLER_CODE}
        isCode
        opacityFrom={0.5}
        opacityTo={0.2}
        fadeStartFrame={TIMING.desatStart}
        fadeDuration={TIMING.desatDuration}
        borderColor={COLORS.codeBorder}
        borderOpacityFrom={0.3}
        borderOpacityTo={0.1}
        textColor={COLORS.codeText}
        textOpacity={0.5}
      />

      {/* "artifact" label below code block */}
      <div
        style={{
          position: 'absolute',
          left: CODE_BLOCK.x,
          top: CODE_BLOCK.y + CODE_BLOCK.height + 12,
          width: CODE_BLOCK.width,
          textAlign: 'center',
          fontFamily: '"Inter", sans-serif',
          fontSize: 11,
          fontStyle: 'italic',
          color: COLORS.codeFaded,
          opacity: artifactLabelOpacity,
        }}
      >
        artifact
      </div>

      {/* Direction arrow — reverses at frame 70 */}
      <DirectionArrow
        startX={ARROW.startX}
        endX={ARROW.endX}
        y={ARROW.y}
      />

      {/* Prompt document (right) — glow intensifies */}
      <EditorWindow
        x={PROMPT_BLOCK.x}
        y={PROMPT_BLOCK.y}
        width={PROMPT_BLOCK.width}
        height={PROMPT_BLOCK.height}
        filename={PROMPT_BLOCK.filename}
        lines={PROMPT_CONTENT}
        isCode={false}
        opacityFrom={0.7}
        opacityTo={0.7}
        fadeStartFrame={TIMING.desatStart}
        fadeDuration={TIMING.desatDuration}
        borderColor={COLORS.promptBlue}
        borderOpacityFrom={0.3}
        borderOpacityTo={0.3}
        borderWidth={2}
        glowColor={COLORS.promptBlue}
        glowFrom={0.06}
        glowTo={0.12}
        textColor={COLORS.promptText}
        textOpacity={0.7}
      />

      {/* "source of truth" label below prompt */}
      <div
        style={{
          position: 'absolute',
          left: PROMPT_BLOCK.x,
          top: PROMPT_BLOCK.y + PROMPT_BLOCK.height + 12,
          width: PROMPT_BLOCK.width,
          textAlign: 'center',
          fontFamily: '"Inter", sans-serif',
          fontSize: 11,
          fontWeight: 700,
          color: COLORS.promptBlue,
          opacity: sourceLabelOpacity,
        }}
      >
        source of truth
      </div>

      {/* Test wall icons */}
      <TestWalls />

      {/* Terminal */}
      <TerminalBlock />

      {/* Callout text at bottom */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          top: 860,
          textAlign: 'center',
          fontFamily: '"Inter", sans-serif',
          fontSize: 16,
          color: COLORS.calloutText,
          opacity: calloutOpacity,
        }}
      >
        The prompt is your new{' '}
        <span
          style={{
            color: COLORS.promptBlue,
            opacity: 0.8 / 0.6, // relative to parent's 0.6 max → effective ~0.8
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
