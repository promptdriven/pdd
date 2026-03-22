import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  HEADER_COLOR,
  TEXT_DEFAULT,
  TEXT_DIM,
  TEST_GREEN,
  MONO_FONT,
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_W,
  TERMINAL_H,
  LAYOUT_FADEIN_END,
  CMD1_START,
  CMD1_TEXT,
  CMD1_OUTPUT,
  CMD2_START,
  CMD2_TEXT,
  CMD2_OUTPUT,
  TESTS_PASS_FRAME,
} from './constants';

const CHAR_DELAY = 2; // frames per character

interface TerminalLineProps {
  startFrame: number;
  command: string;
  output: string;
  outputColor?: string;
}

const TerminalLine: React.FC<TerminalLineProps> = ({
  startFrame,
  command,
  output,
  outputColor = TEXT_DIM,
}) => {
  const frame = useCurrentFrame();

  if (frame < startFrame) return null;

  const elapsed = frame - startFrame;
  const typedLength = Math.min(
    Math.floor(elapsed / CHAR_DELAY),
    command.length
  );
  const typedText = command.slice(0, typedLength);

  // Cursor blink
  const showCursor =
    typedLength < command.length && Math.floor(elapsed / 8) % 2 === 0;

  // Output appears after command is fully typed
  const commandDoneFrame = startFrame + command.length * CHAR_DELAY + 4;
  const showOutput = frame >= commandDoneFrame;

  const outputOpacity = showOutput
    ? interpolate(
        frame,
        [commandDoneFrame, commandDoneFrame + 6],
        [0, 0.85],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : 0;

  return (
    <div style={{ marginBottom: 6 }}>
      <div style={{ display: 'flex', alignItems: 'center', gap: 6 }}>
        <span
          style={{
            fontFamily: MONO_FONT,
            fontSize: 12,
            color: HEADER_COLOR,
            opacity: 0.85,
          }}
        >
          $
        </span>
        <span
          style={{
            fontFamily: MONO_FONT,
            fontSize: 13,
            color: TEXT_DEFAULT,
            opacity: 0.9,
          }}
        >
          {typedText}
          {showCursor && (
            <span style={{ color: TEXT_DEFAULT, opacity: 0.7 }}>▊</span>
          )}
        </span>
      </div>
      {showOutput && (
        <div
          style={{
            fontFamily: MONO_FONT,
            fontSize: 11,
            color: outputColor,
            opacity: outputOpacity,
            paddingLeft: 18,
            marginTop: 2,
          }}
        >
          {output}
        </div>
      )}
    </div>
  );
};

const TerminalStrip: React.FC = () => {
  const frame = useCurrentFrame();

  const layoutOpacity = interpolate(frame, [0, LAYOUT_FADEIN_END], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
  });

  // "All tests passing." line
  const allPassOpacity =
    frame >= TESTS_PASS_FRAME
      ? interpolate(
          frame,
          [TESTS_PASS_FRAME, TESTS_PASS_FRAME + 8],
          [0, 0.9],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        )
      : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: TERMINAL_X,
        top: TERMINAL_Y,
        width: TERMINAL_W,
        height: TERMINAL_H,
        backgroundColor: `rgba(15, 23, 42, 0.6)`,
        borderRadius: 8,
        opacity: layoutOpacity,
        padding: '14px 20px',
        overflow: 'hidden',
      }}
    >
      {/* Terminal header dots */}
      <div
        style={{
          display: 'flex',
          gap: 6,
          marginBottom: 10,
        }}
      >
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#EF4444',
            opacity: 0.6,
          }}
        />
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#F59E0B',
            opacity: 0.6,
          }}
        />
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: '#22C55E',
            opacity: 0.6,
          }}
        />
      </div>

      {/* Command 1 */}
      <TerminalLine
        startFrame={CMD1_START}
        command={CMD1_TEXT}
        output={CMD1_OUTPUT}
      />

      {/* Command 2 */}
      <TerminalLine
        startFrame={CMD2_START}
        command={CMD2_TEXT}
        output={CMD2_OUTPUT}
      />

      {/* All tests passing output */}
      {allPassOpacity > 0 && (
        <div
          style={{
            fontFamily: MONO_FONT,
            fontSize: 11,
            color: TEST_GREEN,
            opacity: allPassOpacity,
            paddingLeft: 18,
            marginTop: 4,
          }}
        >
          All tests passing.
        </div>
      )}
    </div>
  );
};

export default TerminalStrip;
