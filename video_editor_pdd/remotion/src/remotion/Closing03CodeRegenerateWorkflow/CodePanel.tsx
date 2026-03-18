import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  FONTS,
  LAYOUT,
  ORIGINAL_CODE,
  REGENERATED_CODE,
  BUG_LINE_INDEX,
} from './constants';

const LINE_HEIGHT = 22;
const CODE_PADDING_TOP = 44;
const CODE_PADDING_LEFT = 20;

// Character dissolve: each character drifts upward and fades
const DissolveChar: React.FC<{
  char: string;
  color: string;
  charIndex: number;
  lineIndex: number;
  dissolveStart: number;
}> = ({ char, color, charIndex, lineIndex, dissolveStart }) => {
  const frame = useCurrentFrame();
  const delay = dissolveStart + lineIndex * 1 + charIndex * 0.3;
  const duration = 25;

  if (frame < delay) {
    return <span style={{ color }}>{char}</span>;
  }

  const progress = interpolate(frame, [delay, delay + duration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const yOffset = interpolate(progress, [0, 1], [0, -30]);
  const opacity = interpolate(progress, [0, 1], [1, 0]);

  return (
    <span
      style={{
        color,
        display: 'inline-block',
        transform: `translateY(${yOffset}px)`,
        opacity,
      }}
    >
      {char}
    </span>
  );
};

// Stream-in line animation
const StreamLine: React.FC<{
  tokens: Array<{ value: string; color: string }>;
  lineIndex: number;
  streamStart: number;
  lineDelay: number;
}> = ({ tokens, lineIndex, streamStart, lineDelay }) => {
  const frame = useCurrentFrame();
  const lineStart = streamStart + lineIndex * lineDelay;

  const opacity = interpolate(frame, [lineStart, lineStart + 8], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const yOffset = interpolate(frame, [lineStart, lineStart + 8], [6, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  if (frame < lineStart) return null;

  return (
    <div
      style={{
        opacity,
        transform: `translateY(${yOffset}px)`,
        height: LINE_HEIGHT,
        whiteSpace: 'pre',
      }}
    >
      {tokens.map((tok, i) => (
        <span key={i} style={{ color: tok.color }}>
          {tok.value}
        </span>
      ))}
    </div>
  );
};

export const CodePanel: React.FC = () => {
  const frame = useCurrentFrame();
  const { x, y, width, height } = LAYOUT.codePanel;

  // Layout fade-in
  const panelOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Phase: original code visible 0-100, dissolve 100-160, regen 130+
  const isDissolving = frame >= 100 && frame < 160;
  const showOriginal = frame < 130;
  const showRegenerated = frame >= 130;

  // File tab dot color: red before fix, green after
  const dotColor = frame >= 200 ? COLORS.greenCheck : COLORS.red;

  // Dot color transition
  const dotOpacity = frame >= 200
    ? interpolate(frame, [200, 210], [0.5, 1], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      })
    : 1;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
        backgroundColor: `rgba(30, 41, 59, 0.4)`,
        borderRadius: 8,
        opacity: panelOpacity,
        overflow: 'hidden',
      }}
    >
      {/* Header */}
      <div
        style={{
          display: 'flex',
          alignItems: 'center',
          gap: 8,
          padding: '10px 16px',
          borderBottom: '1px solid rgba(100, 116, 139, 0.15)',
        }}
      >
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: dotColor,
            opacity: dotOpacity,
          }}
        />
        <span
          style={{
            fontFamily: FONTS.mono,
            fontSize: 11,
            color: COLORS.textDim,
            opacity: 0.5,
          }}
        >
          user_parser.py
        </span>
      </div>

      {/* Code content */}
      <div
        style={{
          padding: `8px ${CODE_PADDING_LEFT}px`,
          fontFamily: FONTS.mono,
          fontSize: 12,
          lineHeight: `${LINE_HEIGHT}px`,
        }}
      >
        {/* Original code (with dissolve) */}
        {showOriginal &&
          ORIGINAL_CODE.map((line, lineIdx) => {
            const isBugLine = lineIdx === BUG_LINE_INDEX;
            return (
              <div
                key={`orig-${lineIdx}`}
                style={{
                  height: LINE_HEIGHT,
                  whiteSpace: 'pre',
                  position: 'relative',
                  ...(isBugLine
                    ? {
                        backgroundColor: `rgba(239, 68, 68, 0.08)`,
                        borderLeft: `2px solid ${COLORS.red}`,
                        paddingLeft: 8,
                        marginLeft: -10,
                      }
                    : {}),
                }}
              >
                {isDissolving
                  ? line.tokens.map((tok, tIdx) =>
                      tok.value.split('').map((char, cIdx) => (
                        <DissolveChar
                          key={`${tIdx}-${cIdx}`}
                          char={char}
                          color={tok.color}
                          charIndex={
                            line.tokens
                              .slice(0, tIdx)
                              .reduce((a, t) => a + t.value.length, 0) + cIdx
                          }
                          lineIndex={lineIdx}
                          dissolveStart={100}
                        />
                      ))
                    )
                  : line.tokens.map((tok, i) => (
                      <span key={i} style={{ color: tok.color }}>
                        {tok.value}
                      </span>
                    ))}
              </div>
            );
          })}

        {/* Regenerated code (streams in) */}
        {showRegenerated &&
          !showOriginal &&
          REGENERATED_CODE.map((line, lineIdx) => (
            <StreamLine
              key={`regen-${lineIdx}`}
              tokens={line.tokens}
              lineIndex={lineIdx}
              streamStart={130}
              lineDelay={3}
            />
          ))}
      </div>
    </div>
  );
};
