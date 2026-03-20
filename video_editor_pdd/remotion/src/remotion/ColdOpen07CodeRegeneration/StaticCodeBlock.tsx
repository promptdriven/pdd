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
  SELECTION_COLOR,
  SELECTION_OPACITY,
} from './constants';

interface StaticCodeBlockProps {
  /** Lines of code to display */
  codeLines: string[];
  /** Whether to show the selection highlight */
  showSelection: boolean;
  /** 0→1 progress of the selection appearance */
  selectionProgress: number;
}

/**
 * Renders a static block of syntax-highlighted code, optionally
 * with a blue selection highlight overlay on all lines.
 */
export const StaticCodeBlock: React.FC<StaticCodeBlockProps> = ({
  codeLines,
  showSelection,
  selectionProgress,
}) => {
  const selectionOpacity = showSelection
    ? interpolate(selectionProgress, [0, 1], [0, SELECTION_OPACITY], {
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.quad),
      })
    : 0;

  return (
    <div style={{ position: 'absolute', inset: 0 }}>
      {codeLines.map((line, lineIdx) => {
        const y = CODE_TOP_PADDING + lineIdx * LINE_HEIGHT;
        return (
          <div
            key={lineIdx}
            style={{
              position: 'absolute',
              top: y,
              left: GUTTER_WIDTH,
              right: 0,
              height: LINE_HEIGHT,
            }}
          >
            {/* Selection highlight */}
            {selectionOpacity > 0 && (
              <div
                style={{
                  position: 'absolute',
                  inset: 0,
                  backgroundColor: SELECTION_COLOR,
                  opacity: selectionOpacity,
                }}
              />
            )}

            {/* Code text */}
            <span
              style={{
                position: 'absolute',
                left: CODE_LEFT_PADDING,
                top: 0,
                height: LINE_HEIGHT,
                lineHeight: `${LINE_HEIGHT}px`,
                fontFamily: 'JetBrains Mono, monospace',
                fontSize: CODE_FONT_SIZE,
                color: CODE_TEXT_COLOR,
                whiteSpace: 'pre',
              }}
            >
              <SyntaxLine line={line} />
            </span>
          </div>
        );
      })}
    </div>
  );
};
