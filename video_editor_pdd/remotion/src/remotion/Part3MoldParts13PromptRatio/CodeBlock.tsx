import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CODE_X,
  CODE_Y,
  CODE_WIDTH,
  CODE_HEIGHT,
  CODE_BORDER_COLOR,
  CODE_LABEL_COLOR,
  BLOCK_BG_COLOR,
  CODE_LINES,
  BLOCK_FADE_DURATION,
} from './constants';

// Simple syntax highlighting colors
const KEYWORD_COLOR = '#C678DD';
const STRING_COLOR = '#98C379';
const TYPE_COLOR = '#E5C07B';
const COMMENT_COLOR = '#5C6370';
const PUNCTUATION_COLOR = '#ABB2BF';
const DEFAULT_CODE_COLOR = '#ABB2BF';

const keywords = [
  'import',
  'from',
  'export',
  'class',
  'interface',
  'const',
  'async',
  'await',
  'return',
  'if',
  'new',
  'private',
  'constructor',
];
const types = [
  'string',
  'number',
  'boolean',
  'void',
  'Result',
  'AuthContext',
  'TokenPayload',
  'AuthConfig',
  'RedisClient',
  'AuditLogger',
];

function highlightLine(line: string): React.ReactNode[] {
  if (line.trim() === '') return [' '];
  if (line.trim().startsWith('//')) {
    return [
      <span key="c" style={{ color: COMMENT_COLOR }}>
        {line}
      </span>,
    ];
  }

  const tokens = line.split(/(\s+|[{}()[\]:;,.<>=|&?!"+\-*/])/);
  return tokens.map((token, i) => {
    if (keywords.includes(token)) {
      return (
        <span key={i} style={{ color: KEYWORD_COLOR }}>
          {token}
        </span>
      );
    }
    if (types.some((t) => token.includes(t))) {
      return (
        <span key={i} style={{ color: TYPE_COLOR }}>
          {token}
        </span>
      );
    }
    if (token.startsWith('"') || token.startsWith("'")) {
      return (
        <span key={i} style={{ color: STRING_COLOR }}>
          {token}
        </span>
      );
    }
    if (/^[{}()[\]:;,.<>=|&?!+\-*/]$/.test(token)) {
      return (
        <span key={i} style={{ color: PUNCTUATION_COLOR }}>
          {token}
        </span>
      );
    }
    return (
      <span key={i} style={{ color: DEFAULT_CODE_COLOR }}>
        {token}
      </span>
    );
  });
}

export const CodeBlock: React.FC<{ startFrame: number }> = ({
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  const opacity = interpolate(localFrame, [0, BLOCK_FADE_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: CODE_X,
        top: CODE_Y,
        width: CODE_WIDTH,
        opacity,
      }}
    >
      {/* Label above */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: CODE_LABEL_COLOR,
          marginBottom: 6,
        }}
      >
        Generated Code
      </div>

      {/* Badge */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          color: CODE_LABEL_COLOR,
          marginBottom: 8,
        }}
      >
        ~200 lines
      </div>

      {/* Code block */}
      <div
        style={{
          width: CODE_WIDTH,
          height: CODE_HEIGHT,
          backgroundColor: BLOCK_BG_COLOR,
          border: `1px solid ${CODE_BORDER_COLOR}`,
          borderRadius: 8,
          padding: 12,
          overflow: 'hidden',
          boxSizing: 'border-box',
          position: 'relative',
        }}
      >
        {CODE_LINES.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: 'JetBrains Mono, monospace',
              fontSize: 11,
              lineHeight: '14px',
              whiteSpace: 'pre',
              display: 'flex',
              gap: 8,
            }}
          >
            <span
              style={{
                color: '#4B5563',
                minWidth: 24,
                textAlign: 'right',
                userSelect: 'none',
              }}
            >
              {i + 1}
            </span>
            <span>{highlightLine(line)}</span>
          </div>
        ))}

        {/* Scroll fade indicator */}
        <div
          style={{
            position: 'absolute',
            bottom: 0,
            left: 0,
            right: 0,
            height: 80,
            background:
              'linear-gradient(transparent, #1E1E2E)',
            display: 'flex',
            alignItems: 'flex-end',
            justifyContent: 'center',
            paddingBottom: 10,
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 11,
              color: CODE_LABEL_COLOR,
              opacity: 0.6,
            }}
          >
            ... 158 more lines
          </span>
        </div>
      </div>
    </div>
  );
};
