import React from 'react';
import {
  BG_COLOR,
  GUTTER_BG,
  GUTTER_WIDTH,
  GUTTER_TEXT_COLOR,
  CODE_FONT_SIZE,
  CODE_TOP_PADDING,
  LINE_HEIGHT,
} from './constants';

interface EditorChromeProps {
  /** Number of line numbers to display in the gutter */
  lineCount: number;
  children: React.ReactNode;
}

/**
 * Editor chrome shell: dark background + left gutter with line numbers.
 */
export const EditorChrome: React.FC<EditorChromeProps> = ({
  lineCount,
  children,
}) => {
  return (
    <div
      style={{
        position: 'absolute',
        inset: 0,
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Gutter background */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          bottom: 0,
          width: GUTTER_WIDTH,
          backgroundColor: GUTTER_BG,
        }}
      />

      {/* Line numbers */}
      {Array.from({ length: lineCount }, (_, i) => (
        <span
          key={i}
          style={{
            position: 'absolute',
            left: 0,
            top: CODE_TOP_PADDING + i * LINE_HEIGHT,
            width: GUTTER_WIDTH,
            height: LINE_HEIGHT,
            textAlign: 'right',
            paddingRight: 16,
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: CODE_FONT_SIZE,
            lineHeight: `${LINE_HEIGHT}px`,
            color: GUTTER_TEXT_COLOR,
            userSelect: 'none',
            boxSizing: 'border-box',
          }}
        >
          {i + 1}
        </span>
      ))}

      {/* Content area */}
      {children}
    </div>
  );
};
