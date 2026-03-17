import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TERMINAL_POS,
  TERMINAL_SIZE,
  EDITOR_BG,
  TERMINAL_TEXT,
  SUCCESS_GREEN,
  TERMINAL_CMD,
  TERMINAL_ANALYZING,
  TERMINAL_SUCCESS,
} from './constants';

/**
 * Bottom-right terminal panel showing the pdd update command,
 * analysis progress, and success message.
 */
export const TerminalPanel: React.FC<{ startFrame: number }> = ({ startFrame }) => {
  const frame = useCurrentFrame();
  const relFrame = frame - startFrame;

  if (relFrame < 0) return null;

  // Terminal container fades in over 15 frames
  const containerOpacity = interpolate(relFrame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Typing the command starts at relFrame 20 (absolute frame 40)
  // 3 chars per frame => total chars / 3 = frames needed
  const typingStart = 20;
  const charsPerFrame = 3;
  const typingRelFrame = relFrame - typingStart;
  const visibleChars = typingRelFrame > 0
    ? Math.min(Math.floor(typingRelFrame * charsPerFrame), TERMINAL_CMD.length)
    : 0;
  const typedCommand = TERMINAL_CMD.slice(0, visibleChars);
  const showCursor = typingRelFrame > 0 && visibleChars < TERMINAL_CMD.length;

  // "Analyzing module..." appears at relFrame 50 (absolute frame 70)
  const analyzeStart = 50;
  const analyzeOpacity = interpolate(
    relFrame,
    [analyzeStart, analyzeStart + 8],
    [0, 0.4],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Success message at relFrame 120 (absolute frame 140)
  const successStart = 120;
  const successOpacity = interpolate(
    relFrame,
    [successStart, successStart + 8],
    [0, 0.6],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL_POS.x,
        top: TERMINAL_POS.y,
        width: TERMINAL_SIZE.w,
        height: TERMINAL_SIZE.h,
        backgroundColor: EDITOR_BG,
        opacity: containerOpacity,
        borderRadius: 6,
        padding: '12px 14px',
        display: 'flex',
        flexDirection: 'column',
        gap: 6,
        boxShadow: '0 2px 12px rgba(0,0,0,0.3)',
      }}
    >
      {/* Command line */}
      <div
        style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 10,
          color: TERMINAL_TEXT,
          opacity: 0.5,
          whiteSpace: 'pre',
        }}
      >
        {typedCommand}
        {showCursor && (
          <span
            style={{
              display: 'inline-block',
              width: 5,
              height: 12,
              backgroundColor: TERMINAL_TEXT,
              opacity: Math.sin(frame * 0.3) > 0 ? 0.6 : 0,
              marginLeft: 1,
              verticalAlign: 'middle',
            }}
          />
        )}
      </div>

      {/* Analyzing line */}
      {relFrame >= analyzeStart && (
        <div
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 10,
            color: TERMINAL_TEXT,
            opacity: analyzeOpacity,
            whiteSpace: 'pre',
          }}
        >
          {TERMINAL_ANALYZING}
        </div>
      )}

      {/* Success line */}
      {relFrame >= successStart && (
        <div
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 10,
            color: SUCCESS_GREEN,
            opacity: successOpacity,
            whiteSpace: 'pre',
          }}
        >
          {TERMINAL_SUCCESS}
        </div>
      )}
    </div>
  );
};

export default TerminalPanel;
