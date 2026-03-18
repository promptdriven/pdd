import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CMD_BLOCK_Y,
  CMD_BLOCK_WIDTH,
  CMD_BLOCK_BG,
  CMD_BLOCK_BG_OPACITY,
  CMD_BLOCK_BORDER_RADIUS,
  CMD_BLOCK_PADDING_V,
  CMD_BLOCK_PADDING_H,
  CMD_BORDER_LEFT_WIDTH,
  CMD_BORDER_LEFT_COLOR,
  CMD_BORDER_LEFT_OPACITY,
  CMD_FONT_SIZE,
  CMD_LINE_HEIGHT,
  CMD_TEXT_COLOR,
  CMD_TEXT_OPACITY,
  CMD_PROMPT_COLOR,
  CMD_PROMPT_OPACITY,
  CMD_KEYWORD_COLOR,
  CMD_KEYWORD_OPACITY,
  CMD_BLOCK_FADE_START,
  CMD_BLOCK_BG_FADE_DURATION,
  CMD_TYPE_FRAMES_PER_CHAR,
  CMD_LINE_1,
  CMD_LINE_2,
} from './constants';

interface CommandSegment {
  text: string;
  color: string;
  opacity: number;
}

const LINE_1_SEGMENTS: CommandSegment[] = [
  { text: '$ ', color: CMD_PROMPT_COLOR, opacity: CMD_PROMPT_OPACITY },
  { text: 'uv tool install ', color: CMD_TEXT_COLOR, opacity: CMD_TEXT_OPACITY },
  { text: 'pdd-cli', color: CMD_KEYWORD_COLOR, opacity: CMD_KEYWORD_OPACITY },
];

const LINE_2_SEGMENTS: CommandSegment[] = [
  { text: '$ ', color: CMD_PROMPT_COLOR, opacity: CMD_PROMPT_OPACITY },
  { text: 'pdd', color: CMD_KEYWORD_COLOR, opacity: CMD_KEYWORD_OPACITY },
  { text: ' update your_module.py', color: CMD_TEXT_COLOR, opacity: CMD_TEXT_OPACITY },
];

const TypedLine: React.FC<{
  segments: CommandSegment[];
  typeStartFrame: number;
  framesPerChar: number;
}> = ({ segments, typeStartFrame, framesPerChar }) => {
  const frame = useCurrentFrame();

  const fullText = segments.map((s) => s.text).join('');
  const totalChars = fullText.length;

  const elapsed = Math.max(0, frame - typeStartFrame);
  const visibleChars = Math.min(totalChars, Math.floor(elapsed / framesPerChar));

  if (visibleChars <= 0) return null;

  // Build visible segments character by character
  let charCount = 0;
  const renderedSegments: React.ReactNode[] = [];

  for (let i = 0; i < segments.length; i++) {
    const seg = segments[i];
    const segStart = charCount;
    const segEnd = charCount + seg.text.length;

    if (segStart >= visibleChars) break;

    const visibleEnd = Math.min(seg.text.length, visibleChars - segStart);
    const visibleText = seg.text.slice(0, visibleEnd);

    renderedSegments.push(
      <span
        key={i}
        style={{
          color: seg.color,
          opacity: seg.opacity,
        }}
      >
        {visibleText}
      </span>,
    );

    charCount = segEnd;
  }

  // Blinking cursor
  const showCursor = visibleChars < totalChars && Math.floor(frame / 8) % 2 === 0;

  return (
    <div
      style={{
        fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
        fontSize: CMD_FONT_SIZE,
        lineHeight: `${CMD_LINE_HEIGHT}px`,
        whiteSpace: 'pre',
      }}
    >
      {renderedSegments}
      {showCursor && (
        <span style={{ color: CMD_TEXT_COLOR, opacity: 0.6 }}>|</span>
      )}
    </div>
  );
};

export const CommandBlock: React.FC = () => {
  const frame = useCurrentFrame();

  // Background card fade-in
  const bgOpacity = interpolate(
    frame,
    [CMD_BLOCK_FADE_START, CMD_BLOCK_FADE_START + CMD_BLOCK_BG_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Line 1 starts typing after the background has faded in
  const line1TypeStart = CMD_BLOCK_FADE_START + CMD_BLOCK_BG_FADE_DURATION;
  const line1FullText = CMD_LINE_1;
  const line1Duration = line1FullText.length * CMD_TYPE_FRAMES_PER_CHAR;

  // Line 2 starts after line 1 finishes + small delay
  const line2TypeStart = line1TypeStart + line1Duration + 8;

  // Total block height: padding + 2 lines
  const blockHeight = CMD_BLOCK_PADDING_V * 2 + CMD_LINE_HEIGHT * 2;

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'flex-start',
        alignItems: 'center',
        zIndex: 2,
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: CMD_BLOCK_Y - blockHeight / 2,
          width: CMD_BLOCK_WIDTH,
          opacity: bgOpacity,
          backgroundColor: CMD_BLOCK_BG,
          borderRadius: CMD_BLOCK_BORDER_RADIUS,
          padding: `${CMD_BLOCK_PADDING_V}px ${CMD_BLOCK_PADDING_H}px`,
          borderLeft: `${CMD_BORDER_LEFT_WIDTH}px solid rgba(74, 144, 217, ${CMD_BORDER_LEFT_OPACITY})`,
          boxSizing: 'border-box',
        }}
      >
        <TypedLine
          segments={LINE_1_SEGMENTS}
          typeStartFrame={line1TypeStart}
          framesPerChar={CMD_TYPE_FRAMES_PER_CHAR}
        />
        <TypedLine
          segments={LINE_2_SEGMENTS}
          typeStartFrame={line2TypeStart}
          framesPerChar={CMD_TYPE_FRAMES_PER_CHAR}
        />
      </div>
    </AbsoluteFill>
  );
};
