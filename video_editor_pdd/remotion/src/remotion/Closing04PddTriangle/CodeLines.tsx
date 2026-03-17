import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  CANVAS,
  CODE_LINES,
  CODE_LINE_WIDTHS,
  CODE_LINE_OFFSETS,
  TIMING,
} from './constants';

const CodeLines: React.FC = () => {
  const frame = useCurrentFrame();

  const lines = [];
  const totalHeight =
    CODE_LINES.COUNT * CODE_LINES.HEIGHT +
    (CODE_LINES.COUNT - 1) * CODE_LINES.GAP;
  const startY = CANVAS.CENTER.y - totalHeight / 2;

  for (let i = 0; i < CODE_LINES.COUNT; i++) {
    const lineStartFrame =
      TIMING.CODE_LINES_START + i * TIMING.CODE_STAGGER;

    const opacity = interpolate(
      frame,
      [lineStartFrame, lineStartFrame + TIMING.CODE_FADE_DURATION],
      [0, CODE_LINES.OPACITY],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.quad),
      },
    );

    if (opacity <= 0) continue;

    const width = CODE_LINE_WIDTHS[i];
    const xOffset = CODE_LINE_OFFSETS[i];
    const y = startY + i * (CODE_LINES.HEIGHT + CODE_LINES.GAP);
    const x = CANVAS.CENTER.x - width / 2 + xOffset;

    lines.push(
      <div
        key={i}
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width,
          height: CODE_LINES.HEIGHT,
          backgroundColor: CODE_LINES.COLOR,
          opacity,
          borderRadius: 1.5,
        }}
      />,
    );
  }

  return <>{lines}</>;
};

export default CodeLines;
