import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import type { CodeToken, TokenType } from './constants';

/**
 * Renders tokenized code lines with optional per-line flow-in animation.
 */

interface CodeLinesProps {
  lines: CodeToken[][];
  startLineNumber: number;
  lineHeight: number;
  fontSize: number;
  gutterWidth: number;
  paddingTop: number;
  gutterBg: string;
  gutterTextColor: string;
  tokenColorMap: Record<TokenType, string>;
  /** If set, lines animate in one-per-frame starting at this frame */
  flowInStartFrame?: number;
  /** Overall opacity for all lines (used for delete fade) */
  opacity?: number;
}

export const CodeLines: React.FC<CodeLinesProps> = ({
  lines,
  startLineNumber,
  lineHeight,
  fontSize,
  gutterWidth,
  paddingTop,
  gutterBg,
  gutterTextColor,
  tokenColorMap,
  flowInStartFrame,
  opacity = 1,
}) => {
  const frame = useCurrentFrame();

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, right: 0, bottom: 0, opacity }}>
      {/* Gutter background */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: gutterWidth,
          bottom: 0,
          backgroundColor: gutterBg,
        }}
      />

      {lines.map((tokens, i) => {
        const lineNum = startLineNumber + i;

        // Flow-in animation: each line appears at flowInStartFrame + i
        let lineOpacity = 1;
        let translateY = 0;

        if (flowInStartFrame !== undefined) {
          const lineAppearFrame = flowInStartFrame + i;
          // Line is invisible before its appear frame
          if (frame < lineAppearFrame) {
            return null;
          }
          // Animate in with easeOutCubic
          lineOpacity = interpolate(
            frame,
            [lineAppearFrame, lineAppearFrame + 4],
            [0, 1],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.cubic),
            },
          );
          translateY = interpolate(
            frame,
            [lineAppearFrame, lineAppearFrame + 4],
            [8, 0],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.cubic),
            },
          );
        }

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              top: paddingTop + i * lineHeight,
              left: 0,
              right: 0,
              height: lineHeight,
              display: 'flex',
              alignItems: 'center',
              opacity: lineOpacity,
              transform: `translateY(${translateY}px)`,
              willChange: 'opacity, transform',
            }}
          >
            {/* Line number */}
            <span
              style={{
                width: gutterWidth,
                textAlign: 'right',
                paddingRight: 16,
                color: gutterTextColor,
                fontSize: fontSize - 1,
                fontFamily: 'JetBrains Mono, monospace',
                userSelect: 'none',
                flexShrink: 0,
              }}
            >
              {lineNum}
            </span>

            {/* Tokens */}
            <span style={{ fontFamily: 'JetBrains Mono, monospace', fontSize, whiteSpace: 'pre' }}>
              {tokens.map((token, t) => (
                <span key={t} style={{ color: tokenColorMap[token.type] }}>
                  {token.text}
                </span>
              ))}
            </span>
          </div>
        );
      })}
    </div>
  );
};
