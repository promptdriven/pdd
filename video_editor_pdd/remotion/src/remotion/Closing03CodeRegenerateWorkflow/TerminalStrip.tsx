import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, FONTS, LAYOUT } from './constants';

const CHAR_DELAY = 2; // frames per character

interface CommandEntry {
  startFrame: number;
  command: string;
  output: string;
  outputColor?: string;
}

const COMMANDS: CommandEntry[] = [
  {
    startFrame: 30,
    command: 'pdd bug user_parser',
    output: 'Creating failing test...',
  },
  {
    startFrame: 70,
    command: 'pdd fix user_parser',
    output: 'Regenerating...',
  },
];

const FINAL_OUTPUT = {
  startFrame: 160,
  text: 'All tests passing.',
  color: COLORS.greenCheck,
};

const TypedText: React.FC<{
  text: string;
  startFrame: number;
  color: string;
}> = ({ text, startFrame, color }) => {
  const frame = useCurrentFrame();
  if (frame < startFrame) return null;

  const elapsed = frame - startFrame;
  const visibleChars = Math.min(Math.floor(elapsed / CHAR_DELAY), text.length);

  return (
    <span style={{ color }}>
      {text.slice(0, visibleChars)}
      {visibleChars < text.length && (
        <span
          style={{
            display: 'inline-block',
            width: 7,
            height: 14,
            backgroundColor: COLORS.textDefault,
            opacity: 0.7,
            marginLeft: 1,
            verticalAlign: 'middle',
          }}
        />
      )}
    </span>
  );
};

export const TerminalStrip: React.FC = () => {
  const frame = useCurrentFrame();
  const { x, y, width, height } = LAYOUT.terminal;

  // Layout fade-in
  const panelOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
        backgroundColor: `rgba(15, 23, 42, 0.6)`,
        borderRadius: 8,
        opacity: panelOpacity,
        padding: '14px 20px',
        fontFamily: FONTS.mono,
        overflow: 'hidden',
        display: 'flex',
        flexDirection: 'column',
        gap: 6,
      }}
    >
      {COMMANDS.map((cmd, i) => {
        if (frame < cmd.startFrame) return null;
        const cmdEndFrame = cmd.startFrame + cmd.command.length * CHAR_DELAY;
        const outputStart = cmdEndFrame + 4; // small pause after command
        const showOutput = frame >= outputStart;

        return (
          <React.Fragment key={i}>
            {/* Command line */}
            <div style={{ display: 'flex', gap: 8, height: 20 }}>
              <span style={{ color: COLORS.textDim, fontSize: 12 }}>$</span>
              <TypedText
                text={cmd.command}
                startFrame={cmd.startFrame}
                color={COLORS.textDefault}
              />
            </div>

            {/* Output */}
            {showOutput && (
              <div style={{ paddingLeft: 16, height: 18 }}>
                <span
                  style={{
                    color: cmd.outputColor || COLORS.textMuted,
                    fontSize: 11,
                  }}
                >
                  {cmd.output}
                </span>
              </div>
            )}
          </React.Fragment>
        );
      })}

      {/* Final output: "All tests passing." */}
      {frame >= FINAL_OUTPUT.startFrame && (
        <div style={{ paddingLeft: 16, height: 18 }}>
          <span
            style={{
              color: FINAL_OUTPUT.color,
              fontSize: 11,
              opacity: interpolate(
                frame,
                [FINAL_OUTPUT.startFrame, FINAL_OUTPUT.startFrame + 10],
                [0, 1],
                { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
              ),
            }}
          >
            {FINAL_OUTPUT.text}
          </span>
        </div>
      )}
    </div>
  );
};
