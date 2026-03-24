import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CMD_BLOCK_Y,
  CMD_BLOCK_WIDTH,
  CMD_BORDER_LEFT_WIDTH,
  CMD_BORDER_LEFT_COLOR,
  CMD_FONT_SIZE,
  CMD_LINE_HEIGHT,
  CMD_TEXT_COLOR,
  CMD_TEXT_OPACITY,
  CMD_BLOCK_FADE_START,
  CMD_LINE_FADE_DURATION,
  CMD_LINE_2_FADE_START,
  CMD_LINE_1,
  CMD_LINE_2,
} from './constants';

export const CommandBlock: React.FC = () => {
  const frame = useCurrentFrame();

  const line1Opacity = interpolate(
    frame,
    [CMD_BLOCK_FADE_START, CMD_BLOCK_FADE_START + CMD_LINE_FADE_DURATION],
    [0, CMD_TEXT_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const line2Opacity = interpolate(
    frame,
    [CMD_LINE_2_FADE_START, CMD_LINE_2_FADE_START + CMD_LINE_FADE_DURATION],
    [0, CMD_TEXT_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'flex-start',
        alignItems: 'center',
        zIndex: 2,
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: CMD_BLOCK_Y - CMD_LINE_HEIGHT,
          width: CMD_BLOCK_WIDTH,
          borderLeft: `${CMD_BORDER_LEFT_WIDTH}px solid ${CMD_BORDER_LEFT_COLOR}33`,
          paddingLeft: 16,
          boxSizing: 'border-box',
          display: 'flex',
          flexDirection: 'column',
        }}
      >
        <div
          style={{
            fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
            fontSize: CMD_FONT_SIZE,
            lineHeight: `${CMD_LINE_HEIGHT}px`,
            whiteSpace: 'pre',
            color: CMD_TEXT_COLOR,
            opacity: line1Opacity,
          }}
        >
          {CMD_LINE_1}
        </div>
        <div
          style={{
            fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
            fontSize: CMD_FONT_SIZE,
            lineHeight: `${CMD_LINE_HEIGHT}px`,
            whiteSpace: 'pre',
            color: CMD_TEXT_COLOR,
            opacity: line2Opacity,
          }}
        >
          {CMD_LINE_2}
        </div>
      </div>
    </AbsoluteFill>
  );
};
