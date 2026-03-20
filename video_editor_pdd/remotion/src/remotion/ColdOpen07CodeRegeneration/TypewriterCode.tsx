import React from 'react';
import { interpolate, Easing } from 'remotion';
import { SyntaxLine } from './SyntaxHighlighter';
import {
  GUTTER_WIDTH,
  CODE_LEFT_PADDING,
  CODE_TOP_PADDING,
  LINE_HEIGHT,
  CODE_FONT_SIZE,
  CODE_TEXT_COLOR,
  CHARS_PER_SECOND,
  FPS,
  ENTRANCE_GLOW_COLOR,
  ENTRANCE_GLOW_OPACITY,
  ENTRANCE_GLOW_FADE_FRAMES,
} from './constants';

interface TypewriterCodeProps {
  /** Lines of code to type in */
  codeLines: string[];
  /** Relative frame within the regeneration phase (0 = first char appears) */
  phaseFrame: number;
}

export const TypewriterCode: React.FC<TypewriterCodeProps> = ({
  codeLines,
  phaseFrame,
}) => {
  const charsPerFrame = CHARS_PER_SECOND / FPS; // 60/30 = 2 chars per frame

  // Pre-compute the cumulative char offset where each line starts typing
  const lineStartChars: number[] = [];
  let cumChars = 0;
  for (const line of codeLines) {
    lineStartChars.push(cumChars);
    // Each line costs its length + 1 (for the "enter" beat at the end)
    cumChars += Math.max(line.length, 1) + 1;
  }

  const totalCharsTyped = phaseFrame * charsPerFrame;

  return (
    <div style={{ position: 'absolute', inset: 0 }}>
      {codeLines.map((line, lineIdx) => {
        const lineStart = lineStartChars[lineIdx];

        // How many chars into this line have been typed
        const charsIntoLine = totalCharsTyped - lineStart;
        if (charsIntoLine < 0) return null; // not yet reached

        const visibleChars = Math.min(Math.floor(charsIntoLine), line.length);

        // Frame when this line started appearing
        const lineStartFrame = lineStart / charsPerFrame;
        const lineAge = phaseFrame - lineStartFrame;

        // Entrance glow: brief green background that fades
        const glowOpacity = interpolate(
          lineAge,
          [0, ENTRANCE_GLOW_FADE_FRAMES],
          [ENTRANCE_GLOW_OPACITY, 0],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        const y = CODE_TOP_PADDING + lineIdx * LINE_HEIGHT;

        return (
          <div
            key={lineIdx}
            style={{
              position: 'absolute',
              top: y,
              left: 0,
              right: 0,
              height: LINE_HEIGHT,
              display: 'flex',
              alignItems: 'center',
            }}
          >
            {/* Entrance glow background */}
            {glowOpacity > 0 && (
              <div
                style={{
                  position: 'absolute',
                  left: GUTTER_WIDTH,
                  right: 0,
                  top: 0,
                  bottom: 0,
                  backgroundColor: ENTRANCE_GLOW_COLOR,
                  opacity: glowOpacity,
                  pointerEvents: 'none',
                }}
              />
            )}

            {/* Code text */}
            <span
              style={{
                position: 'absolute',
                left: GUTTER_WIDTH + CODE_LEFT_PADDING,
                fontFamily: 'JetBrains Mono, monospace',
                fontSize: CODE_FONT_SIZE,
                color: CODE_TEXT_COLOR,
                whiteSpace: 'pre',
              }}
            >
              <SyntaxLine line={line} visibleChars={visibleChars} />
            </span>
          </div>
        );
      })}
    </div>
  );
};
