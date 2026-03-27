import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  PROMPT_X,
  PROMPT_Y,
  PROMPT_WIDTH,
  PROMPT_HEIGHT,
  PROMPT_COLOR,
  BLOCK_BG_COLOR,
  PROMPT_LINES,
  BLOCK_FADE_DURATION,
} from './constants';

export const PromptBlock: React.FC<{ startFrame: number }> = ({
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
        left: PROMPT_X,
        top: PROMPT_Y,
        width: PROMPT_WIDTH,
        opacity,
      }}
    >
      {/* Label above */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: PROMPT_COLOR,
          marginBottom: 6,
        }}
      >
        Prompt
      </div>

      {/* Badge */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          color: PROMPT_COLOR,
          opacity: 0.5,
          marginBottom: 8,
        }}
      >
        ~15 lines
      </div>

      {/* Block */}
      <div
        style={{
          width: PROMPT_WIDTH,
          height: PROMPT_HEIGHT,
          backgroundColor: BLOCK_BG_COLOR,
          border: `1px solid rgba(217, 148, 74, 0.3)`,
          borderRadius: 8,
          padding: 12,
          overflow: 'hidden',
          boxSizing: 'border-box',
        }}
      >
        {PROMPT_LINES.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: 'JetBrains Mono, monospace',
              fontSize: 11,
              color: PROMPT_COLOR,
              opacity: 0.7,
              lineHeight: '13px',
              whiteSpace: 'nowrap',
              overflow: 'hidden',
              textOverflow: 'ellipsis',
            }}
          >
            {line}
          </div>
        ))}
      </div>
    </div>
  );
};
