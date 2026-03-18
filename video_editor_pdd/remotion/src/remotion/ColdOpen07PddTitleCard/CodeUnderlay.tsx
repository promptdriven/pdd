import React from 'react';
import { interpolate, useCurrentFrame } from 'remotion';
import {
  CANVAS,
  COLORS,
  CODE_LINES,
  CODE_UNDERLAY_OPACITY_START,
  CODE_UNDERLAY_OPACITY_END,
  TIMING,
} from './constants';

// Minimal syntax coloring for the code underlay
const SYNTAX_COLORS: Record<string, string> = {
  keyword: '#C678DD',
  string: '#98C379',
  type: '#E5C07B',
  function: '#61AFEF',
  punctuation: '#ABB2BF',
  default: '#ABB2BF',
};

function colorizeToken(token: string): { text: string; color: string } {
  const keywords = [
    'export', 'async', 'function', 'const', 'await', 'if', 'return',
  ];
  const types = ['string', 'Schema', 'AST'];

  if (keywords.includes(token)) return { text: token, color: SYNTAX_COLORS.keyword };
  if (types.includes(token)) return { text: token, color: SYNTAX_COLORS.type };
  if (token.startsWith("'") || token.startsWith('"')) return { text: token, color: SYNTAX_COLORS.string };
  if (/^[a-zA-Z]+\(/.test(token)) return { text: token, color: SYNTAX_COLORS.function };
  return { text: token, color: SYNTAX_COLORS.default };
}

export const CodeUnderlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Dim from 0.08 to 0.04 over first 20 frames
  const opacity = interpolate(
    frame,
    [TIMING.QUESTION_FADE_START, TIMING.QUESTION_FADE_END],
    [CODE_UNDERLAY_OPACITY_START, CODE_UNDERLAY_OPACITY_END],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: CANVAS.WIDTH,
        height: CANVAS.HEIGHT,
        opacity,
        overflow: 'hidden',
        pointerEvents: 'none',
      }}
    >
      {CODE_LINES.map((line, i) => (
        <div
          key={i}
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 14,
            lineHeight: '22px',
            color: COLORS.QUESTION_TEXT,
            whiteSpace: 'pre',
            paddingLeft: 120,
            paddingTop: i === 0 ? 80 : 0,
          }}
        >
          <span style={{ color: '#636D83', marginRight: 24, userSelect: 'none' }}>
            {String(i + 1).padStart(2, ' ')}
          </span>
          {line.split(/(\s+)/).map((token, j) => {
            const { color } = colorizeToken(token.trim());
            return (
              <span key={j} style={{ color: token.trim() ? color : undefined }}>
                {token}
              </span>
            );
          })}
        </div>
      ))}
    </div>
  );
};
