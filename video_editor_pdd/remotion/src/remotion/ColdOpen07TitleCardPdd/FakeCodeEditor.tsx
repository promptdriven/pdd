// Sub-component: simulated code-editor background
// Represents the "inherited" regenerated code from spec 06
import React from 'react';
import { AbsoluteFill } from 'remotion';
import {
  EDITOR_BG,
  EDITOR_GUTTER,
  EDITOR_LINE_NUMBER,
  CODE_KEYWORD,
  CODE_STRING,
  CODE_FUNCTION,
  CODE_COMMENT,
  CODE_TEXT,
  CODE_BRACKET,
  CODE_TYPE,
} from './constants';

/** Inline code lines representing freshly-regenerated output */
const CODE_LINES: { indent: number; tokens: { text: string; color: string }[] }[] = [
  { indent: 0, tokens: [{ text: 'import', color: CODE_KEYWORD }, { text: ' React ', color: CODE_TEXT }, { text: 'from', color: CODE_KEYWORD }, { text: " 'react'", color: CODE_STRING }] },
  { indent: 0, tokens: [{ text: 'import', color: CODE_KEYWORD }, { text: ' { motion } ', color: CODE_TEXT }, { text: 'from', color: CODE_KEYWORD }, { text: " 'framer-motion'", color: CODE_STRING }] },
  { indent: 0, tokens: [] },
  { indent: 0, tokens: [{ text: '// Auto-generated component', color: CODE_COMMENT }] },
  { indent: 0, tokens: [{ text: 'export', color: CODE_KEYWORD }, { text: ' const ', color: CODE_KEYWORD }, { text: 'AnimatedCard', color: CODE_FUNCTION }, { text: ': ', color: CODE_TEXT }, { text: 'React.FC', color: CODE_TYPE }, { text: ' = (', color: CODE_BRACKET }, { text: '{ title, desc }', color: CODE_TEXT }, { text: ') => {', color: CODE_BRACKET }] },
  { indent: 1, tokens: [{ text: 'const', color: CODE_KEYWORD }, { text: ' [isHovered, setHovered] = ', color: CODE_TEXT }, { text: 'useState', color: CODE_FUNCTION }, { text: '(', color: CODE_BRACKET }, { text: 'false', color: CODE_KEYWORD }, { text: ')', color: CODE_BRACKET }] },
  { indent: 0, tokens: [] },
  { indent: 1, tokens: [{ text: 'return', color: CODE_KEYWORD }, { text: ' (', color: CODE_BRACKET }] },
  { indent: 2, tokens: [{ text: '<motion.div', color: CODE_TYPE }] },
  { indent: 3, tokens: [{ text: 'whileHover', color: CODE_FUNCTION }, { text: '={{ scale: ', color: CODE_TEXT }, { text: '1.02', color: CODE_STRING }, { text: ' }}', color: CODE_TEXT }] },
  { indent: 3, tokens: [{ text: 'className', color: CODE_FUNCTION }, { text: '=', color: CODE_TEXT }, { text: '"card-container"', color: CODE_STRING }] },
  { indent: 2, tokens: [{ text: '>', color: CODE_TYPE }] },
  { indent: 3, tokens: [{ text: '<h2', color: CODE_TYPE }, { text: '>{title}', color: CODE_TEXT }, { text: '</h2>', color: CODE_TYPE }] },
  { indent: 3, tokens: [{ text: '<p', color: CODE_TYPE }, { text: '>{desc}', color: CODE_TEXT }, { text: '</p>', color: CODE_TYPE }] },
  { indent: 3, tokens: [{ text: '{isHovered && (', color: CODE_TEXT }] },
  { indent: 4, tokens: [{ text: '<motion.span', color: CODE_TYPE }] },
  { indent: 5, tokens: [{ text: 'initial', color: CODE_FUNCTION }, { text: '={{ opacity: ', color: CODE_TEXT }, { text: '0', color: CODE_STRING }, { text: ' }}', color: CODE_TEXT }] },
  { indent: 5, tokens: [{ text: 'animate', color: CODE_FUNCTION }, { text: '={{ opacity: ', color: CODE_TEXT }, { text: '1', color: CODE_STRING }, { text: ' }}', color: CODE_TEXT }] },
  { indent: 4, tokens: [{ text: '>', color: CODE_TYPE }] },
  { indent: 5, tokens: [{ text: 'View Details →', color: CODE_STRING }] },
  { indent: 4, tokens: [{ text: '</motion.span>', color: CODE_TYPE }] },
  { indent: 3, tokens: [{ text: ')}', color: CODE_TEXT }] },
  { indent: 2, tokens: [{ text: '</motion.div>', color: CODE_TYPE }] },
  { indent: 1, tokens: [{ text: ')', color: CODE_BRACKET }] },
  { indent: 0, tokens: [{ text: '}', color: CODE_BRACKET }] },
];

const LINE_HEIGHT = 28;
const FONT_SIZE = 16;
const GUTTER_WIDTH = 60;
const INDENT_PX = 24;
const FIRST_LINE_NUMBER = 1;

export const FakeCodeEditor: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: EDITOR_BG,
        fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
        fontSize: FONT_SIZE,
        lineHeight: `${LINE_HEIGHT}px`,
        overflow: 'hidden',
      }}
    >
      {/* Editor tab bar */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          right: 0,
          height: 40,
          backgroundColor: '#010409',
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 16,
          gap: 0,
        }}
      >
        <div
          style={{
            backgroundColor: EDITOR_BG,
            color: CODE_TEXT,
            padding: '8px 20px',
            fontSize: 13,
            borderTop: '2px solid #58A6FF',
            borderRadius: '0',
          }}
        >
          AnimatedCard.tsx
        </div>
        <div
          style={{
            color: EDITOR_LINE_NUMBER,
            padding: '8px 20px',
            fontSize: 13,
          }}
        >
          index.ts
        </div>
      </div>

      {/* Code area */}
      <div
        style={{
          position: 'absolute',
          top: 40,
          left: 0,
          right: 0,
          bottom: 0,
        }}
      >
        {CODE_LINES.map((line, i) => (
          <div
            key={i}
            style={{
              display: 'flex',
              height: LINE_HEIGHT,
              alignItems: 'center',
            }}
          >
            {/* Gutter */}
            <div
              style={{
                width: GUTTER_WIDTH,
                textAlign: 'right',
                paddingRight: 16,
                color: EDITOR_LINE_NUMBER,
                backgroundColor: EDITOR_GUTTER,
                fontSize: 14,
                userSelect: 'none',
                flexShrink: 0,
                height: '100%',
                display: 'flex',
                alignItems: 'center',
                justifyContent: 'flex-end',
              }}
            >
              {FIRST_LINE_NUMBER + i}
            </div>

            {/* Code tokens */}
            <div
              style={{
                paddingLeft: 12 + line.indent * INDENT_PX,
                whiteSpace: 'pre',
                display: 'flex',
              }}
            >
              {line.tokens.map((tok, j) => (
                <span key={j} style={{ color: tok.color }}>
                  {tok.text}
                </span>
              ))}
            </div>
          </div>
        ))}
      </div>
    </AbsoluteFill>
  );
};

export default FakeCodeEditor;
