import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_W,
  TERMINAL_H,
  TERMINAL_BG,
  TEXT_DIM,
  SUCCESS_GREEN,
  TERMINAL_COMMAND,
  TERMINAL_ANALYZING,
  TERMINAL_SUCCESS,
} from './constants';

const TerminalPanel: React.FC<{ startFrame: number }> = ({ startFrame }) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - startFrame;

  if (relativeFrame < 0) return null;

  // Terminal fades in over 15 frames
  const terminalOpacity = interpolate(relativeFrame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Command typing starts at relative frame 20
  // 3 characters per frame, total chars in command
  const typingStart = 20;
  const typingFrame = relativeFrame - typingStart;
  const commandChars = typingFrame > 0 ? Math.min(
    Math.floor(typingFrame * 3),
    TERMINAL_COMMAND.length,
  ) : 0;
  const typedCommand = TERMINAL_COMMAND.substring(0, commandChars);
  const showCursor = typingFrame >= 0 && commandChars < TERMINAL_COMMAND.length;

  // "Analyzing module..." appears at relative frame 50
  const analyzingFrame = relativeFrame - 50;
  const analyzingOpacity = interpolate(analyzingFrame, [0, 8], [0, 0.4], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Success line appears at relative frame 140
  const successRelFrame = relativeFrame - 120; // 120 frames after terminal start = frame 140
  const successOpacity = interpolate(successRelFrame, [0, 8], [0, 0.6], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL_X - TERMINAL_W / 2,
        top: TERMINAL_Y - TERMINAL_H / 2,
        width: TERMINAL_W,
        height: TERMINAL_H,
        backgroundColor: TERMINAL_BG,
        opacity: terminalOpacity * 0.85,
        borderRadius: 6,
        padding: '12px 14px',
        display: 'flex',
        flexDirection: 'column',
        gap: 6,
        boxShadow: '0 4px 16px rgba(0, 0, 0, 0.3)',
      }}
    >
      {/* Command line */}
      <div
        style={{
          fontFamily: '"JetBrains Mono", monospace',
          fontSize: 10,
          color: TEXT_DIM,
          opacity: 0.5,
          whiteSpace: 'nowrap',
        }}
      >
        {typedCommand}
        {showCursor && (
          <span
            style={{
              opacity: Math.sin(frame * 0.3) > 0 ? 1 : 0,
              color: TEXT_DIM,
            }}
          >
            ▋
          </span>
        )}
      </div>

      {/* Analyzing line */}
      {analyzingFrame >= 0 && (
        <div
          style={{
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 10,
            color: TEXT_DIM,
            opacity: analyzingOpacity,
            whiteSpace: 'nowrap',
          }}
        >
          {TERMINAL_ANALYZING}
        </div>
      )}

      {/* Success line */}
      {successRelFrame >= 0 && (
        <div
          style={{
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 10,
            color: SUCCESS_GREEN,
            opacity: successOpacity,
            whiteSpace: 'nowrap',
          }}
        >
          {TERMINAL_SUCCESS}
        </div>
      )}
    </div>
  );
};

export default TerminalPanel;
