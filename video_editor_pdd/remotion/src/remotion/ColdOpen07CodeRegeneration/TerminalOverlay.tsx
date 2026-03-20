import React from 'react';
import { interpolate, Easing } from 'remotion';
import {
  TERMINAL_BG,
  TERMINAL_BORDER_COLOR,
  TERMINAL_TEXT_COLOR,
  TERMINAL_FONT_SIZE,
  CHECKMARK_COLOR,
  TERMINAL_COMMAND,
  TERMINAL_RESULT,
  TERMINAL_FADE_FRAMES,
  FPS,
} from './constants';

// ── Component ───────────────────────────────────────────────────────────────

interface TerminalOverlayProps {
  /** Frame offset within the terminal phase (0 = terminal start) */
  phaseFrame: number;
}

const TerminalOverlay: React.FC<TerminalOverlayProps> = ({ phaseFrame }) => {
  // Fade in over TERMINAL_FADE_FRAMES
  const containerOpacity = interpolate(
    phaseFrame,
    [0, TERMINAL_FADE_FRAMES],
    [0, 1],
    { extrapolateRight: 'clamp', extrapolateLeft: 'clamp', easing: Easing.out(Easing.cubic) },
  );

  // Command types in after fade (chars per frame at 60 c/s)
  const commandStartFrame = TERMINAL_FADE_FRAMES;
  const commandCharsPerFrame = 60 / FPS;
  const commandCharsVisible =
    phaseFrame > commandStartFrame
      ? Math.min(
          Math.floor((phaseFrame - commandStartFrame) * commandCharsPerFrame),
          TERMINAL_COMMAND.length,
        )
      : 0;

  const commandText = TERMINAL_COMMAND.slice(0, commandCharsVisible);
  const commandFullyTyped = commandCharsVisible >= TERMINAL_COMMAND.length;

  // Checkmark appears 5 frames after command is fully typed
  const checkmarkDelay = 5;
  const showCheckmark =
    commandFullyTyped && phaseFrame > commandStartFrame + TERMINAL_COMMAND.length / commandCharsPerFrame + checkmarkDelay;

  return (
    <div
      style={{
        position: 'absolute',
        right: 40,
        bottom: 20,
        width: 480,
        minHeight: 50,
        background: TERMINAL_BG,
        opacity: containerOpacity,
        borderRadius: 8,
        border: `1px solid ${TERMINAL_BORDER_COLOR}66`, // 0.4 opacity
        padding: '12px 16px',
        display: 'flex',
        alignItems: 'center',
        fontFamily: '"JetBrains Mono", monospace',
        fontSize: TERMINAL_FONT_SIZE,
      }}
    >
      <span style={{ color: TERMINAL_TEXT_COLOR, whiteSpace: 'pre' }}>
        {commandText}
      </span>
      {showCheckmark && (
        <span style={{ color: CHECKMARK_COLOR, marginLeft: 6, fontWeight: 700 }}>
          {TERMINAL_RESULT}
        </span>
      )}
    </div>
  );
};

export default TerminalOverlay;
