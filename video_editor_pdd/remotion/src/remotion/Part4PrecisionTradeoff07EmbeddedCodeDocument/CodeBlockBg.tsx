import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, EDITOR } from './constants';

interface CodeBlockBgProps {
  startFrame: number;
  yOffset: number;
  height: number;
}

export const CodeBlockBg: React.FC<CodeBlockBgProps> = ({
  startFrame,
  yOffset,
  height,
}) => {
  const frame = useCurrentFrame();
  const elapsed = Math.max(0, frame - startFrame);

  // Slide in with easeOut(cubic) over 15 frames
  const progress = interpolate(elapsed, [0, 15], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateRight: 'clamp',
    extrapolateLeft: 'clamp',
  });

  const opacity = progress;
  const scaleY = interpolate(progress, [0, 1], [0.8, 1]);

  return (
    <div
      style={{
        position: 'absolute',
        top: yOffset,
        left: EDITOR.gutterWidth - 2,
        right: 0,
        height: height,
        backgroundColor: COLORS.codeBlockBg,
        opacity,
        transform: `scaleY(${scaleY})`,
        transformOrigin: 'top center',
        borderLeft: `3px solid ${COLORS.codeBorder}4D`, // 0.3 opacity = 4D hex
      }}
    />
  );
};
