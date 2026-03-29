import React from 'react';
import {
  TOKEN_COLORS,
  CODE_FONT_FAMILY,
  CODE_FONT_SIZE,
  CODE_LINE_HEIGHT,
  EDITOR_PADDING_LEFT,
  GUTTER_WIDTH,
  LINE_NUMBER_COLOR,
  EDITOR_GUTTER_BG,
} from './constants';
import type { Token } from './constants';

interface CodeLineProps {
  tokens: Token[];
  lineNumber: number;
  opacity?: number;
  yOffset?: number;
}

const CodeLine: React.FC<CodeLineProps> = ({
  tokens,
  lineNumber,
  opacity = 1,
  yOffset = 0,
}) => {
  const y = (lineNumber - 1) * CODE_LINE_HEIGHT;

  return (
    <div
      style={{
        position: 'absolute',
        top: y,
        left: 0,
        width: '100%',
        height: CODE_LINE_HEIGHT,
        display: 'flex',
        alignItems: 'center',
        opacity,
        transform: `translateY(${yOffset}px)`,
        fontFamily: CODE_FONT_FAMILY,
        fontSize: CODE_FONT_SIZE,
        lineHeight: `${CODE_LINE_HEIGHT}px`,
        whiteSpace: 'pre',
      }}
    >
      {/* Line number gutter */}
      <div
        style={{
          width: GUTTER_WIDTH,
          minWidth: GUTTER_WIDTH,
          textAlign: 'right',
          paddingRight: 16,
          color: LINE_NUMBER_COLOR,
          backgroundColor: EDITOR_GUTTER_BG,
          height: '100%',
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'flex-end',
          userSelect: 'none',
        }}
      >
        {lineNumber}
      </div>
      {/* Code content */}
      <div
        style={{
          paddingLeft: EDITOR_PADDING_LEFT - GUTTER_WIDTH,
          display: 'flex',
          alignItems: 'center',
          height: '100%',
        }}
      >
        {tokens.map((token, i) => (
          <span
            key={i}
            style={{
              color: TOKEN_COLORS[token.type],
            }}
          >
            {token.text}
          </span>
        ))}
      </div>
    </div>
  );
};

export default CodeLine;
