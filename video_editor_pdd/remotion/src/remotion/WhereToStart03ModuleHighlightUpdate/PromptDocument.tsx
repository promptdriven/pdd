import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  PROMPT_POS,
  PROMPT_SIZE,
  TITLE_BAR_H,
  SELECTION_BLUE,
  BLOCK_FILL,
  EDITOR_BG,
  TEXT_MUTED,
  PROMPT_LINES,
} from './constants';

/**
 * The .prompt file document that materializes as particles arrive.
 * Window chrome + staggered lines of natural language.
 */
export const PromptDocument: React.FC<{ startFrame: number }> = ({ startFrame }) => {
  const frame = useCurrentFrame();
  const relFrame = frame - startFrame;

  if (relFrame < 0) return null;

  // Document frame fades in over 20 frames
  const docOpacity = interpolate(relFrame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Ambient glow grows in
  const glowOpacity = interpolate(relFrame, [0, 40], [0, 0.06], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(3)),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: PROMPT_POS.x,
        top: PROMPT_POS.y,
        width: PROMPT_SIZE.w,
        height: PROMPT_SIZE.h,
        opacity: docOpacity,
        boxShadow: `0 0 16px rgba(74, 144, 217, ${glowOpacity})`,
        borderRadius: 6,
        overflow: 'hidden',
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: TITLE_BAR_H,
          backgroundColor: BLOCK_FILL,
          borderTopLeftRadius: 6,
          borderTopRightRadius: 6,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 10,
          gap: 6,
        }}
      >
        {/* Window dots */}
        <div style={{ width: 6, height: 6, borderRadius: '50%', backgroundColor: '#EF4444', opacity: 0.4 }} />
        <div style={{ width: 6, height: 6, borderRadius: '50%', backgroundColor: '#EAB308', opacity: 0.4 }} />
        <div style={{ width: 6, height: 6, borderRadius: '50%', backgroundColor: '#22C55E', opacity: 0.4 }} />
        <span
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 10,
            color: SELECTION_BLUE,
            opacity: 0.6,
            marginLeft: 8,
          }}
        >
          auth_handler.prompt
        </span>
      </div>

      {/* Editor body */}
      <div
        style={{
          backgroundColor: EDITOR_BG,
          height: PROMPT_SIZE.h - TITLE_BAR_H,
          padding: '8px 12px',
          overflow: 'hidden',
        }}
      >
        {PROMPT_LINES.map((line, idx) => {
          // Lines appear staggered: 8 frames per line, starting 10 frames after document appears
          const lineStart = 10 + idx * 8;
          const lineOpacity = interpolate(
            relFrame,
            [lineStart, lineStart + 8],
            [0, 0.6],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            },
          );

          const lineTranslateY = interpolate(
            relFrame,
            [lineStart, lineStart + 8],
            [4, 0],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            },
          );

          const isHeading = line.startsWith('#');

          return (
            <div
              key={idx}
              style={{
                fontFamily: isHeading ? 'JetBrains Mono, monospace' : 'Inter, sans-serif',
                fontSize: isHeading ? 11 : 9,
                fontWeight: isHeading ? 600 : 400,
                color: isHeading ? SELECTION_BLUE : TEXT_MUTED,
                opacity: lineOpacity,
                transform: `translateY(${lineTranslateY}px)`,
                lineHeight: '14px',
                whiteSpace: 'nowrap',
                overflow: 'hidden',
                textOverflow: 'ellipsis',
              }}
            >
              {line}
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default PromptDocument;
