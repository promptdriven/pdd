import React from 'react';
import { interpolate, Easing } from 'remotion';
import {
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_BG,
  TERMINAL_BORDER_COLOR,
  TERMINAL_TEXT_COLOR,
  TERMINAL_CHECK_COLOR,
  TERMINAL_FONT_SIZE,
} from './constants';

interface TerminalOverlayProps {
  /** Relative frame within the terminal phase (0 = start of fade-in) */
  phaseFrame: number;
}

export const TerminalOverlay: React.FC<TerminalOverlayProps> = ({
  phaseFrame,
}) => {
  // Fade in over 15 frames with easeOut cubic
  const containerOpacity = interpolate(phaseFrame, [0, 15], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Command types in after fade-in completes
  const commandText = '$ pdd generate processUserInput';
  const typewriterCharsPerFrame = 2; // fast typing
  const commandStart = 15; // start typing after fade-in
  const commandFrame = Math.max(0, phaseFrame - commandStart);
  const visibleCommandChars = Math.min(
    Math.floor(commandFrame * typewriterCharsPerFrame),
    commandText.length
  );

  // Checkmark appears after command is fully typed
  const commandDoneFrame = commandStart + Math.ceil(commandText.length / typewriterCharsPerFrame);
  const showCheckmark = phaseFrame >= commandDoneFrame + 5; // small pause

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL_X,
        top: TERMINAL_Y,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        opacity: containerOpacity,
        borderRadius: 8,
        border: `1px solid ${TERMINAL_BORDER_COLOR}`,
        display: 'flex',
        alignItems: 'center',
        paddingLeft: 16,
        paddingRight: 16,
        boxSizing: 'border-box',
      }}
    >
      <span
        style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: TERMINAL_FONT_SIZE,
          color: TERMINAL_TEXT_COLOR,
          whiteSpace: 'pre',
        }}
      >
        {commandText.slice(0, visibleCommandChars)}
      </span>
      {showCheckmark && (
        <span
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: TERMINAL_FONT_SIZE,
            color: TERMINAL_CHECK_COLOR,
            marginLeft: 8,
            fontWeight: 700,
          }}
        >
          ✓
        </span>
      )}
    </div>
  );
};
