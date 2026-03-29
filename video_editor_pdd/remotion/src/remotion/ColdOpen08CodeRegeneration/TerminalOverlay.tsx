import React from 'react';
import {
  TERMINAL_BG,
  TERMINAL_TEXT,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_RADIUS,
  TERMINAL_FONT_SIZE,
  TERMINAL_COMMAND,
  CODE_FONT_FAMILY,
} from './constants';

interface TerminalOverlayProps {
  opacity: number;
  checkmarkGlow: number;
}

const TerminalOverlay: React.FC<TerminalOverlayProps> = ({
  opacity,
  checkmarkGlow,
}) => {
  if (opacity <= 0) return null;

  // Split into command part and checkmark
  const commandPart = '$ pdd generate process_order ';
  const checkmark = '✓';

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 40,
        right: 40,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        opacity: Math.max(opacity, 0) * 0.9,
        borderRadius: TERMINAL_RADIUS,
        display: 'flex',
        alignItems: 'center',
        paddingLeft: 16,
        paddingRight: 16,
        fontFamily: CODE_FONT_FAMILY,
        fontSize: TERMINAL_FONT_SIZE,
        color: TERMINAL_TEXT,
        boxShadow: `0 4px 20px rgba(0, 0, 0, 0.4)`,
      }}
    >
      <span>{commandPart}</span>
      <span
        style={{
          textShadow:
            checkmarkGlow > 0
              ? `0 0 ${8 * checkmarkGlow}px ${TERMINAL_TEXT}, 0 0 ${16 * checkmarkGlow}px ${TERMINAL_TEXT}`
              : 'none',
        }}
      >
        {checkmark}
      </span>
    </div>
  );
};

export default TerminalOverlay;
