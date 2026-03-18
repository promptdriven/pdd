import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  PROMPT_X,
  PROMPT_Y,
  PROMPT_W,
  PROMPT_H,
  PROMPT_TITLE_BAR_H,
  PROMPT_LINES,
  BLOCK_FILL,
  EDITOR_BG,
  BLUE_ACCENT,
  TEXT_MUTED,
} from './constants';

const PromptDocument: React.FC<{ startFrame: number }> = ({ startFrame }) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - startFrame;

  if (relativeFrame < 0) return null;

  // Document frame materializes: scale from 0.9 to 1, opacity 0 to 1
  const docOpacity = interpolate(relativeFrame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  const docScale = interpolate(relativeFrame, [0, 20], [0.92, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Document glow ramps up
  const glowOpacity = interpolate(relativeFrame, [20, 60], [0, 0.06], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: PROMPT_X - PROMPT_W / 2,
        top: PROMPT_Y - PROMPT_H / 2,
        width: PROMPT_W,
        height: PROMPT_H,
        opacity: docOpacity,
        transform: `scale(${docScale})`,
        borderRadius: 6,
        overflow: 'hidden',
        boxShadow: `0 0 16px rgba(74, 144, 217, ${glowOpacity}), 0 4px 24px rgba(0, 0, 0, 0.4)`,
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: PROMPT_TITLE_BAR_H,
          backgroundColor: BLOCK_FILL,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 10,
          borderTopLeftRadius: 6,
          borderTopRightRadius: 6,
        }}
      >
        {/* Window dots */}
        <div style={{ display: 'flex', gap: 4, marginRight: 8 }}>
          <div style={{ width: 6, height: 6, borderRadius: '50%', backgroundColor: '#3B3B3B' }} />
          <div style={{ width: 6, height: 6, borderRadius: '50%', backgroundColor: '#3B3B3B' }} />
          <div style={{ width: 6, height: 6, borderRadius: '50%', backgroundColor: '#3B3B3B' }} />
        </div>
        <span
          style={{
            fontFamily: '"JetBrains Mono", monospace',
            fontSize: 10,
            color: BLUE_ACCENT,
            opacity: 0.6,
          }}
        >
          auth_handler.prompt
        </span>
      </div>

      {/* Editor body */}
      <div
        style={{
          backgroundColor: EDITOR_BG,
          height: PROMPT_H - PROMPT_TITLE_BAR_H,
          padding: '8px 12px',
          display: 'flex',
          flexDirection: 'column',
          gap: 2,
          overflow: 'hidden',
        }}
      >
        {PROMPT_LINES.map((line, i) => {
          // Lines appear staggered: 8 frames per line, starting after document materializes
          const lineStartFrame = 15 + i * 8;
          const lineOpacity = interpolate(
            relativeFrame,
            [lineStartFrame, lineStartFrame + 8],
            [0, 0.6],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            },
          );

          const lineTranslateY = interpolate(
            relativeFrame,
            [lineStartFrame, lineStartFrame + 8],
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
              key={i}
              style={{
                fontFamily: isHeading ? '"JetBrains Mono", monospace' : 'Inter, sans-serif',
                fontSize: isHeading ? 11 : 9,
                color: isHeading ? BLUE_ACCENT : TEXT_MUTED,
                opacity: lineOpacity,
                transform: `translateY(${lineTranslateY}px)`,
                fontWeight: isHeading ? 600 : 400,
                lineHeight: '14px',
                whiteSpace: 'nowrap',
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
