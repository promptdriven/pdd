import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  TERMINAL_CENTER_X,
  TERMINAL_CENTER_Y,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_BG,
  TERMINAL_BG_OPACITY,
  TERMINAL_TEXT,
  TERMINAL_PROMPT_COLOR,
  CHECK_COLOR,
} from './constants';

interface TerminalStripProps {
  command: string;
  result: string;
  /** Global frame at which terminal typing begins */
  typeStartFrame: number;
  /** Global frame at which check/result appears */
  checkStartFrame: number;
}

const TerminalStrip: React.FC<TerminalStripProps> = ({
  command,
  result,
  typeStartFrame,
  checkStartFrame,
}) => {
  const frame = useCurrentFrame();

  // Terminal typing: 2 frames per character
  const cmdProgress = Math.max(0, frame - typeStartFrame);
  const cmdCharsShown = Math.min(command.length, Math.floor(cmdProgress / 2));

  // Check mark pop animation (easeOut back overshoot)
  const checkLocalFrame = frame - checkStartFrame;
  const checkScale =
    checkLocalFrame < 0
      ? 0
      : interpolate(checkLocalFrame, [0, 8], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.back(1.7)),
        });

  const showResult = frame >= checkStartFrame;
  const showCommand = frame >= typeStartFrame;

  if (!showCommand) return null;

  // Split result into check mark and rest
  const checkMark = result.startsWith('✓') ? '✓' : '';
  const resultText = result.startsWith('✓') ? result.slice(1) : result;

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL_CENTER_X - TERMINAL_WIDTH / 2,
        top: TERMINAL_CENTER_Y - TERMINAL_HEIGHT / 2,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        opacity: TERMINAL_BG_OPACITY,
        borderRadius: '0 0 4px 4px',
        display: 'flex',
        alignItems: 'center',
        paddingLeft: 12,
        paddingRight: 12,
        boxSizing: 'border-box',
        overflow: 'hidden',
      }}
    >
      {!showResult ? (
        <span
          style={{
            fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
            fontSize: 12,
            fontWeight: 400,
            whiteSpace: 'pre',
          }}
        >
          <span style={{ color: TERMINAL_PROMPT_COLOR }}>$ </span>
          <span style={{ color: TERMINAL_TEXT }}>
            {command.slice(0, cmdCharsShown)}
          </span>
          {/* Blinking cursor */}
          {cmdCharsShown < command.length && (
            <span
              style={{
                color: TERMINAL_TEXT,
                opacity: frame % 16 < 8 ? 1 : 0,
              }}
            >
              █
            </span>
          )}
        </span>
      ) : (
        <span
          style={{
            fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
            fontSize: 12,
            fontWeight: 400,
            whiteSpace: 'pre',
          }}
        >
          {checkMark && (
            <span
              style={{
                color: CHECK_COLOR,
                fontSize: 14,
                fontWeight: 700,
                display: 'inline-block',
                transform: `scale(${checkScale})`,
                transformOrigin: 'center',
              }}
            >
              {checkMark}
            </span>
          )}
          <span style={{ color: TERMINAL_TEXT }}>{resultText}</span>
        </span>
      )}
    </div>
  );
};

export default TerminalStrip;
