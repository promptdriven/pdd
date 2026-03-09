import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION, PROMPT_TEXT } from './constants';

export const TypewriterText: React.FC = () => {
  const frame = useCurrentFrame();

  // Characters visible so far (linear typing)
  const charCount = Math.floor(
    interpolate(
      frame,
      [ANIMATION.typeStart, ANIMATION.typeEnd],
      [0, PROMPT_TEXT.length],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      }
    )
  );

  const visibleText = PROMPT_TEXT.slice(0, charCount);

  // Cursor blink: visible in first half of each blink cycle
  const cursorPhase = (frame % ANIMATION.cursorBlinkRate) / ANIMATION.cursorBlinkRate;
  const showCursor = frame >= ANIMATION.typeStart && cursorPhase < 0.5;

  // Wrap text into lines for line numbers (~40 chars per line at 20px in 948-120px panel)
  const maxCharsPerLine = 38;
  const lines = wrapText(visibleText, maxCharsPerLine);
  const totalLines = wrapText(PROMPT_TEXT, maxCharsPerLine);

  return (
    <div
      style={{
        position: 'absolute',
        left: DIMENSIONS.promptPadding,
        top: 380,
        right: DIMENSIONS.promptPadding,
        display: 'flex',
        flexDirection: 'row',
        zIndex: 2,
      }}
    >
      {/* Line number gutter */}
      <div
        style={{
          width: DIMENSIONS.lineNumberGutterWidth,
          flexShrink: 0,
          display: 'flex',
          flexDirection: 'column',
          userSelect: 'none',
        }}
      >
        {totalLines.map((_, i) => (
          <div
            key={i}
            style={{
              fontFamily: TYPOGRAPHY.lineNumber.fontFamily,
              fontSize: TYPOGRAPHY.lineNumber.fontSize,
              color: COLORS.lineNumber,
              lineHeight: `${TYPOGRAPHY.prompt.fontSize * TYPOGRAPHY.prompt.lineHeight}px`,
              textAlign: 'right',
              paddingRight: 16,
              opacity: i < lines.length ? 1 : 0.3,
            }}
          >
            {i + 1}
          </div>
        ))}
      </div>

      {/* Prompt text area */}
      <div
        style={{
          flex: 1,
          fontFamily: TYPOGRAPHY.prompt.fontFamily,
          fontSize: TYPOGRAPHY.prompt.fontSize,
          color: COLORS.promptText,
          lineHeight: TYPOGRAPHY.prompt.lineHeight,
          whiteSpace: 'pre-wrap',
          wordBreak: 'break-word',
        }}
      >
        {visibleText}
        {showCursor && (
          <span
            style={{
              display: 'inline-block',
              width: 10,
              height: TYPOGRAPHY.prompt.fontSize,
              backgroundColor: COLORS.cursorColor,
              marginLeft: 1,
              verticalAlign: 'text-bottom',
            }}
          />
        )}
      </div>
    </div>
  );
};

function wrapText(text: string, maxChars: number): string[] {
  const words = text.split(' ');
  const lines: string[] = [];
  let current = '';

  for (const word of words) {
    if (current.length + word.length + (current ? 1 : 0) > maxChars && current) {
      lines.push(current);
      current = word;
    } else {
      current = current ? `${current} ${word}` : word;
    }
  }
  if (current) lines.push(current);
  if (lines.length === 0) lines.push('');

  return lines;
}
