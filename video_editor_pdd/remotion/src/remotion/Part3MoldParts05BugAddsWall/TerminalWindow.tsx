import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_BG,
  TERMINAL_BORDER,
  TERMINAL_GREEN,
  TERMINAL_GRAY,
  TERMINAL_FADE_IN_START,
  TERMINAL_FADE_IN_DURATION,
  TERMINAL_CMD2_FRAME,
  TERMINAL_CMD3_FRAME,
  TERMINAL_CMD4_FRAME,
  TERMINAL_FADE_OUT_START,
  TERMINAL_FADE_OUT_DURATION,
} from './constants';

interface TerminalCommand {
  text: string;
  isPrompt: boolean;
  color: string;
  showAtFrame: number;
}

const COMMANDS: TerminalCommand[] = [
  {
    text: '$ pdd bug user_parser',
    isPrompt: true,
    color: TERMINAL_GREEN,
    showAtFrame: TERMINAL_FADE_IN_START,
  },
  {
    text: 'Creating failing test...',
    isPrompt: false,
    color: TERMINAL_GREEN,
    showAtFrame: TERMINAL_CMD2_FRAME,
  },
  {
    text: '$ pdd fix user_parser',
    isPrompt: true,
    color: TERMINAL_GREEN,
    showAtFrame: TERMINAL_CMD3_FRAME,
  },
  {
    text: 'All tests passing ✓',
    isPrompt: false,
    color: TERMINAL_GREEN,
    showAtFrame: TERMINAL_CMD4_FRAME,
  },
];

export const TerminalWindow: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in
  const fadeInOpacity = interpolate(
    frame,
    [TERMINAL_FADE_IN_START, TERMINAL_FADE_IN_START + TERMINAL_FADE_IN_DURATION],
    [0, 1],
    { easing: Easing.out(Easing.quad), extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Fade out
  const fadeOutOpacity = interpolate(
    frame,
    [TERMINAL_FADE_OUT_START, TERMINAL_FADE_OUT_START + TERMINAL_FADE_OUT_DURATION],
    [1, 0.5],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const opacity = Math.min(fadeInOpacity, fadeOutOpacity);

  if (opacity <= 0) return null;

  // Determine visible commands
  const visibleCommands = COMMANDS.filter((cmd) => frame >= cmd.showAtFrame);

  // Typing animation for the latest command
  const renderCommandText = (cmd: TerminalCommand, isLatest: boolean) => {
    if (!isLatest) return cmd.text;

    const elapsed = frame - cmd.showAtFrame;
    const charsPerFrame = 1.5;
    const visibleChars = Math.min(
      Math.floor(elapsed * charsPerFrame),
      cmd.text.length
    );
    return cmd.text.slice(0, visibleChars);
  };

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL_X,
        top: TERMINAL_Y,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        border: `1px solid ${TERMINAL_BORDER}`,
        borderRadius: 6,
        opacity,
        padding: 12,
        overflow: 'hidden',
        display: 'flex',
        flexDirection: 'column',
        justifyContent: 'flex-end',
        gap: 6,
      }}
    >
      {/* Title bar dots */}
      <div
        style={{
          position: 'absolute',
          top: 8,
          left: 12,
          display: 'flex',
          gap: 6,
        }}
      >
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#FF5F57',
            opacity: 0.7,
          }}
        />
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#FEBC2E',
            opacity: 0.7,
          }}
        />
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#28C840',
            opacity: 0.7,
          }}
        />
      </div>

      {/* Commands */}
      <div style={{ marginTop: 20, display: 'flex', flexDirection: 'column', gap: 4 }}>
        {visibleCommands.map((cmd, i) => {
          const isLatest = i === visibleCommands.length - 1;
          const displayText = renderCommandText(cmd, isLatest);

          return (
            <div
              key={`cmd-${cmd.showAtFrame}`}
              style={{
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 12,
                lineHeight: '18px',
                whiteSpace: 'nowrap',
              }}
            >
              {cmd.isPrompt ? (
                <>
                  <span style={{ color: TERMINAL_GRAY }}>$ </span>
                  <span style={{ color: cmd.color }}>
                    {displayText.startsWith('$ ') ? displayText.slice(2) : displayText}
                  </span>
                </>
              ) : (
                <span style={{ color: cmd.color }}>{displayText}</span>
              )}
              {/* Blinking cursor on latest command */}
              {isLatest && (
                <span
                  style={{
                    color: TERMINAL_GREEN,
                    opacity: Math.sin(frame * 0.3) > 0 ? 1 : 0,
                  }}
                >
                  ▌
                </span>
              )}
            </div>
          );
        })}
      </div>
    </div>
  );
};
