import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  HEADER_COLOR,
  MONO_FONT,
  CODE_PANEL_X,
  CODE_PANEL_Y,
  CODE_PANEL_W,
  CODE_PANEL_H,
  ORIGINAL_CODE,
  REGENERATED_CODE,
  BUG_LINE_INDEX,
  BUG_RED,
  PASS_GREEN,
  LAYOUT_FADEIN_END,
  DISSOLVE_START,
  DISSOLVE_END,
  STREAM_START,
  ANNOTATION_START,
  CodeToken,
} from './constants';

/**
 * Generates deterministic pseudo-random values for particle scatter effect.
 */
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 9301 + 4927) * 49297;
  return x - Math.floor(x);
}

interface CharParticle {
  char: string;
  color: string;
  x: number;
  y: number;
  driftX: number;
  driftY: number;
  delay: number;
}

const CodePanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Layout fade in
  const layoutOpacity = interpolate(frame, [0, LAYOUT_FADEIN_END], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
  });

  // File tab dot color: red until annotation, then green
  const dotColorTransition = interpolate(
    frame,
    [ANNOTATION_START, ANNOTATION_START + 10],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const dotColor = dotColorTransition < 0.5 ? BUG_RED : PASS_GREEN;

  // Dissolve phase (frame 100-130)
  const isDissolving = frame >= DISSOLVE_START && frame < STREAM_START;
  // Show original code before dissolve, regenerated after stream-in start
  const showOriginal = frame < DISSOLVE_START;
  const showRegenerated = frame >= STREAM_START;

  // Build character particles for dissolve effect
  const particles = useMemo(() => {
    const chars: CharParticle[] = [];
    const lineHeight = 28;
    const charWidth = 8.4;
    const startY = 50;
    const startX = 20;
    let idx = 0;

    ORIGINAL_CODE.forEach((tokens: CodeToken[], lineIdx: number) => {
      let col = 0;
      tokens.forEach((token: CodeToken) => {
        for (let c = 0; c < token.text.length; c++) {
          chars.push({
            char: token.text[c],
            color: token.color,
            x: startX + col * charWidth,
            y: startY + lineIdx * lineHeight,
            driftX: (seededRandom(idx * 3 + 1) - 0.5) * 60,
            driftY: -(seededRandom(idx * 3 + 2) * 40 + 20),
            delay: idx,
          });
          col++;
          idx++;
        }
      });
    });
    return chars;
  }, []);

  // Total chars for stagger calculation
  const totalChars = particles.length;

  // Render code lines (static)
  const renderCodeLines = (
    lines: CodeToken[][],
    bugLine: number | null,
    globalOpacity: number
  ) => {
    const lineHeight = 28;
    const startY = 50;
    const startX = 20;

    return lines.map((tokens, lineIdx) => {
      const isBugLine = bugLine !== null && lineIdx === bugLine;
      return (
        <div
          key={lineIdx}
          style={{
            position: 'absolute',
            top: startY + lineIdx * lineHeight,
            left: 0,
            right: 0,
            height: lineHeight,
            display: 'flex',
            alignItems: 'center',
            paddingLeft: startX,
            backgroundColor: isBugLine
              ? `rgba(239, 68, 68, 0.08)`
              : 'transparent',
            borderLeft: isBugLine ? `2px solid ${BUG_RED}` : '2px solid transparent',
            opacity: globalOpacity,
          }}
        >
          {tokens.map((token, tIdx) => (
            <span
              key={tIdx}
              style={{
                fontFamily: MONO_FONT,
                fontSize: 12,
                color: token.color,
                opacity: 0.85,
                whiteSpace: 'pre',
              }}
            >
              {token.text}
            </span>
          ))}
        </div>
      );
    });
  };

  // Stream-in animation for regenerated code
  const renderStreamingCode = () => {
    const lineHeight = 28;
    const startY = 50;
    const startX = 20;
    const lineStagger = 3;

    return REGENERATED_CODE.map((tokens, lineIdx) => {
      const lineStart = STREAM_START + lineIdx * lineStagger;
      const lineOpacity = interpolate(
        frame,
        [lineStart, lineStart + 8],
        [0, 0.85],
        {
          easing: Easing.out(Easing.quad),
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        }
      );
      const lineY = interpolate(
        frame,
        [lineStart, lineStart + 8],
        [startY + lineIdx * lineHeight - 10, startY + lineIdx * lineHeight],
        {
          easing: Easing.out(Easing.quad),
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        }
      );

      return (
        <div
          key={lineIdx}
          style={{
            position: 'absolute',
            top: lineY,
            left: 0,
            right: 0,
            height: lineHeight,
            display: 'flex',
            alignItems: 'center',
            paddingLeft: startX,
            opacity: lineOpacity,
          }}
        >
          {tokens.map((token, tIdx) => (
            <span
              key={tIdx}
              style={{
                fontFamily: MONO_FONT,
                fontSize: 12,
                color: token.color,
                whiteSpace: 'pre',
              }}
            >
              {token.text}
            </span>
          ))}
        </div>
      );
    });
  };

  // Render dissolving particles
  const renderDissolve = () => {
    const dissolveDuration = DISSOLVE_END - DISSOLVE_START;
    const maxDelay = totalChars;

    return particles.map((p, i) => {
      // Normalize delay to fit within dissolve window
      const charDelay = (p.delay / maxDelay) * (dissolveDuration * 0.6);
      const charStart = DISSOLVE_START + charDelay;
      const charEnd = charStart + 15;

      const opacity = interpolate(frame, [charStart, charEnd], [0.85, 0], {
        easing: Easing.in(Easing.quad),
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      });

      const driftProgress = interpolate(
        frame,
        [charStart, charEnd],
        [0, 1],
        {
          easing: Easing.in(Easing.quad),
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        }
      );

      if (opacity <= 0) return null;

      return (
        <span
          key={i}
          style={{
            position: 'absolute',
            left: p.x + p.driftX * driftProgress,
            top: p.y + p.driftY * driftProgress,
            fontFamily: MONO_FONT,
            fontSize: 12,
            color: p.color,
            opacity,
            pointerEvents: 'none',
          }}
        >
          {p.char}
        </span>
      );
    });
  };

  return (
    <div
      style={{
        position: 'absolute',
        left: CODE_PANEL_X,
        top: CODE_PANEL_Y,
        width: CODE_PANEL_W,
        height: CODE_PANEL_H,
        backgroundColor: `rgba(30, 41, 59, 0.4)`,
        borderRadius: 8,
        opacity: layoutOpacity,
        overflow: 'hidden',
      }}
    >
      {/* Header bar */}
      <div
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: 8,
          padding: '10px 16px',
          borderBottom: '1px solid rgba(100, 116, 139, 0.15)',
        }}
      >
        {/* File tab dot */}
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: dotColor,
            transition: 'background-color 0.3s',
          }}
        />
        <span
          style={{
            fontFamily: MONO_FONT,
            fontSize: 11,
            color: HEADER_COLOR,
            opacity: 0.8,
          }}
        >
          user_parser.py
        </span>
      </div>

      {/* Code content area */}
      <div style={{ position: 'relative', width: '100%', height: CODE_PANEL_H - 40 }}>
        {showOriginal && renderCodeLines(ORIGINAL_CODE, BUG_LINE_INDEX, 1)}
        {isDissolving && renderDissolve()}
        {showRegenerated && renderStreamingCode()}
      </div>
    </div>
  );
};

export default CodePanel;
