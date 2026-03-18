import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CODE_LINES,
  CODE_COLOR,
  CODE_OPACITY_FROM,
  CODE_OPACITY_TO,
  CODE_DIM_DURATION,
  CODE_DIM_START,
  TRIANGLE_CENTER,
} from './constants';

const LINE_HEIGHT = 22;
const FONT_SIZE = 14;

export const CodeLinesFading: React.FC = () => {
  const frame = useCurrentFrame();

  // Dimming starts at CODE_DIM_START
  const localFrame = Math.max(0, frame - CODE_DIM_START);

  const opacity = interpolate(
    localFrame,
    [0, CODE_DIM_DURATION],
    [CODE_OPACITY_FROM, CODE_OPACITY_TO],
    { extrapolateRight: 'clamp', easing: Easing.in(Easing.quad) }
  );

  const totalHeight = CODE_LINES.length * LINE_HEIGHT;
  const startY = TRIANGLE_CENTER[1] - totalHeight / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: TRIANGLE_CENTER[0] - 200,
        top: startY,
        width: 400,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        opacity,
      }}
    >
      {CODE_LINES.map((line, i) => (
        <div
          key={i}
          style={{
            fontFamily: '"JetBrains Mono", "Fira Code", monospace',
            fontSize: FONT_SIZE,
            color: CODE_COLOR,
            lineHeight: `${LINE_HEIGHT}px`,
            whiteSpace: 'pre',
            textAlign: 'left',
            width: '100%',
          }}
        >
          {line}
        </div>
      ))}
    </div>
  );
};
