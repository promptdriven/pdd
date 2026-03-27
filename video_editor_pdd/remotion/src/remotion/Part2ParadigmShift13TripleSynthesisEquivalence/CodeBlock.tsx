import React from 'react';
import {
  CODE_BG_COLOR,
  CODE_X,
  CODE_Y,
  CODE_WIDTH,
  CODE_HEIGHT,
  CODE_TEXT_COLOR,
  KEYWORD_COLOR,
  TYPE_COLOR,
  COMMENT_COLOR,
  CANVAS_WIDTH,
} from './constants';

/**
 * Simple syntax-highlighted Verilog code block.
 * Rendered as styled <pre> with manual coloring of keywords.
 */
const CodeBlock: React.FC = () => {
  // Manually highlight the Verilog code for deterministic rendering
  const lines: Array<{ segments: Array<{ text: string; color: string }> }> = [
    {
      segments: [
        { text: 'module', color: KEYWORD_COLOR },
        { text: ' alu(', color: CODE_TEXT_COLOR },
      ],
    },
    {
      segments: [
        { text: '  ', color: CODE_TEXT_COLOR },
        { text: 'input', color: KEYWORD_COLOR },
        { text: '  [', color: CODE_TEXT_COLOR },
        { text: '7:0', color: TYPE_COLOR },
        { text: '] a, b,', color: CODE_TEXT_COLOR },
      ],
    },
    {
      segments: [
        { text: '  ', color: CODE_TEXT_COLOR },
        { text: 'input', color: KEYWORD_COLOR },
        { text: '  [', color: CODE_TEXT_COLOR },
        { text: '1:0', color: TYPE_COLOR },
        { text: '] op,', color: CODE_TEXT_COLOR },
      ],
    },
    {
      segments: [
        { text: '  ', color: CODE_TEXT_COLOR },
        { text: 'output', color: KEYWORD_COLOR },
        { text: ' [', color: CODE_TEXT_COLOR },
        { text: '7:0', color: TYPE_COLOR },
        { text: '] result', color: CODE_TEXT_COLOR },
      ],
    },
    {
      segments: [{ text: ');', color: CODE_TEXT_COLOR }],
    },
    {
      segments: [
        { text: '  ', color: CODE_TEXT_COLOR },
        { text: 'assign', color: KEYWORD_COLOR },
        { text: ' result = (op==0) ? a+b :', color: CODE_TEXT_COLOR },
      ],
    },
    {
      segments: [
        { text: '    (op==1) ? a-b :', color: CODE_TEXT_COLOR },
      ],
    },
    {
      segments: [
        { text: '    (op==2) ? a&b : a|b;', color: CODE_TEXT_COLOR },
      ],
    },
    {
      segments: [
        { text: 'endmodule', color: KEYWORD_COLOR },
      ],
    },
  ];

  return (
    <div
      style={{
        position: 'absolute',
        left: (CANVAS_WIDTH - CODE_WIDTH) / 2,
        top: CODE_Y,
        width: CODE_WIDTH,
        height: CODE_HEIGHT,
        backgroundColor: CODE_BG_COLOR,
        borderRadius: 8,
        padding: '10px 16px',
        boxSizing: 'border-box',
        overflow: 'hidden',
        border: '1px solid rgba(100, 116, 139, 0.3)',
      }}
    >
      <pre
        style={{
          margin: 0,
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 11,
          lineHeight: 1.35,
          whiteSpace: 'pre',
        }}
      >
        {lines.map((line, li) => (
          <div key={li}>
            {line.segments.map((seg, si) => (
              <span key={si} style={{ color: seg.color }}>
                {seg.text}
              </span>
            ))}
          </div>
        ))}
      </pre>
    </div>
  );
};

export default CodeBlock;
