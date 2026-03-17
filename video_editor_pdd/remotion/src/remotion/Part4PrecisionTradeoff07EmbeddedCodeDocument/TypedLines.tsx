import React from 'react';
import { useCurrentFrame } from 'remotion';
import { COLORS, EDITOR, FONTS, CHARS_PER_FRAME } from './constants';

interface TypedLinesProps {
  lines: string[];
  startFrame: number;
  startLineNumber: number;
  isCode?: boolean;
}

export const TypedLines: React.FC<TypedLinesProps> = ({
  lines,
  startFrame,
  startLineNumber,
  isCode = false,
}) => {
  const frame = useCurrentFrame();
  const elapsed = Math.max(0, frame - startFrame);

  // Calculate cumulative character counts for each line
  const lineCumChars: number[] = [];
  let total = 0;
  for (const line of lines) {
    total += line.length;
    lineCumChars.push(total);
  }

  // Total characters typed so far
  const totalTyped = elapsed * CHARS_PER_FRAME;

  return (
    <>
      {lines.map((line, idx) => {
        const lineStart = idx === 0 ? 0 : lineCumChars[idx - 1];
        const charsIntoLine = Math.max(0, Math.min(line.length, totalTyped - lineStart));
        const visibleText = line.substring(0, charsIntoLine);
        const lineComplete = charsIntoLine >= line.length;
        const lineNum = startLineNumber + idx;

        if (charsIntoLine <= 0 && totalTyped < lineStart) return null;

        const yOffset = (lineNum - 1) * EDITOR.lineHeight;

        return (
          <div
            key={idx}
            style={{
              position: 'absolute',
              top: 12 + yOffset,
              left: 0,
              right: 0,
              height: EDITOR.lineHeight,
              display: 'flex',
              alignItems: 'center',
            }}
          >
            {/* Line number */}
            <span
              style={{
                width: EDITOR.gutterWidth,
                textAlign: 'right',
                paddingRight: 10,
                fontFamily: FONTS.mono,
                fontSize: 10,
                color: COLORS.lineNumber,
                opacity: 0.25,
                flexShrink: 0,
                userSelect: 'none',
              }}
            >
              {lineNum}
            </span>

            {/* Line content */}
            <span
              style={{
                fontFamily: isCode ? FONTS.mono : FONTS.sans,
                fontSize: isCode ? 11 : 13,
                color: isCode ? COLORS.codeText : COLORS.naturalText,
                opacity: isCode ? 0.7 : 0.8,
                whiteSpace: 'pre',
                position: 'relative',
              }}
            >
              {visibleText}
              {/* Typing cursor */}
              {!lineComplete && charsIntoLine > 0 && (
                <span
                  style={{
                    display: 'inline-block',
                    width: 2,
                    height: isCode ? 13 : 15,
                    backgroundColor: isCode ? COLORS.codeText : COLORS.intentLabel,
                    opacity: 0.7,
                    marginLeft: 1,
                    verticalAlign: 'middle',
                  }}
                />
              )}
            </span>

            {/* Ambient glow for natural language lines (not code) */}
            {!isCode && lineComplete && (
              <div
                style={{
                  position: 'absolute',
                  top: 0,
                  left: EDITOR.gutterWidth,
                  right: 0,
                  height: EDITOR.lineHeight,
                  background: `radial-gradient(ellipse at center, ${COLORS.ambientGlow}08 0%, transparent 70%)`,
                  filter: 'blur(10px)',
                  pointerEvents: 'none',
                }}
              />
            )}
          </div>
        );
      })}
    </>
  );
};
