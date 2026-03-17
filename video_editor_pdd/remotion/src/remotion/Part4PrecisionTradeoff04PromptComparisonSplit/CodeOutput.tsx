import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { MONO_FONT, SANS_FONT, COLORS, CANVAS_WIDTH } from './constants';

const CodeOutput: React.FC<{
  codeLines: string[];
  startFrame: number;
  y: number;
}> = ({ codeLines, startFrame, y }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [startFrame, startFrame + 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const translateY = interpolate(frame, [startFrame, startFrame + 20], [15, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const panelWidth = 440;
  const codeBlockStyle: React.CSSProperties = {
    width: panelWidth,
    padding: '8px 12px',
    backgroundColor: 'rgba(15, 23, 42, 0.8)',
    borderRadius: 4,
    border: '1px solid rgba(51, 65, 85, 0.2)',
  };

  const renderCodeBlock = (xOffset: number) => (
    <div
      style={{
        position: 'absolute',
        left: xOffset,
        top: 0,
        ...codeBlockStyle,
      }}
    >
      {codeLines.map((line, i) => (
        <div
          key={i}
          style={{
            fontFamily: MONO_FONT,
            fontSize: 9,
            color: COLORS.outputCodeColor,
            opacity: 0.3,
            lineHeight: '14px',
            whiteSpace: 'pre',
          }}
        >
          {line}
        </div>
      ))}
    </div>
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: y,
        width: CANVAS_WIDTH,
        height: 130,
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      {/* Left code block */}
      {renderCodeBlock(40)}

      {/* Right code block */}
      {renderCodeBlock(CANVAS_WIDTH / 2 + 40)}

      {/* Center label */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          bottom: 0,
          textAlign: 'center',
        }}
      >
        <span
          style={{
            fontFamily: SANS_FONT,
            fontSize: 13,
            color: COLORS.bottomLabel,
            opacity: 0.5,
          }}
        >
          Same output. Different specification strategy.
        </span>
      </div>
    </div>
  );
};

export default CodeOutput;
