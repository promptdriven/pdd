import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { FONTS } from './constants';

interface BracketLabelProps {
  text: string;
  color: string;
  startFrame: number;
  yTop: number;
  yBottom: number;
  x: number;
  pulseStart?: number;
  pulseEnd?: number;
}

export const BracketLabel: React.FC<BracketLabelProps> = ({
  text,
  color,
  startFrame,
  yTop,
  yBottom,
  x,
  pulseStart = 340,
  pulseEnd = 420,
}) => {
  const frame = useCurrentFrame();
  const elapsed = Math.max(0, frame - startFrame);

  // Bracket draw: easeOut(quad) over 20 frames
  const drawProgress = interpolate(elapsed, [0, 20], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
    extrapolateLeft: 'clamp',
  });

  // Label text fade in slightly after bracket starts
  const textOpacity = interpolate(elapsed, [10, 25], [0, 0.5], {
    extrapolateRight: 'clamp',
    extrapolateLeft: 'clamp',
  });

  // Pulse during label pulse phase
  const inPulsePhase = frame >= pulseStart && frame <= pulseEnd;
  let pulseOpacity = 0;
  if (inPulsePhase) {
    const pulseElapsed = frame - pulseStart;
    const pulseDuration = pulseEnd - pulseStart;
    pulseOpacity = interpolate(
      pulseElapsed,
      [0, pulseDuration / 2, pulseDuration],
      [0, 0.15, 0],
      {
        easing: Easing.inOut(Easing.sin),
        extrapolateRight: 'clamp',
      }
    );
  }

  const bracketHeight = (yBottom - yTop) * drawProgress;
  const bracketWidth = 12;
  const midY = yTop + (yBottom - yTop) / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: yTop,
        width: 200,
        height: yBottom - yTop,
        opacity: drawProgress > 0 ? 1 : 0,
      }}
    >
      {/* Bracket SVG */}
      <svg
        width={bracketWidth + 2}
        height={yBottom - yTop}
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          overflow: 'visible',
        }}
      >
        {/* Top horizontal tick */}
        <line
          x1={0}
          y1={0}
          x2={bracketWidth * drawProgress}
          y2={0}
          stroke={color}
          strokeWidth={1.5}
          opacity={0.5}
        />
        {/* Vertical line */}
        <line
          x1={0}
          y1={0}
          x2={0}
          y2={bracketHeight}
          stroke={color}
          strokeWidth={1.5}
          opacity={0.5}
        />
        {/* Bottom horizontal tick */}
        {drawProgress >= 0.8 && (
          <line
            x1={0}
            y1={bracketHeight}
            x2={bracketWidth * Math.min(1, (drawProgress - 0.8) / 0.2)}
            y2={bracketHeight}
            stroke={color}
            strokeWidth={1.5}
            opacity={0.5}
          />
        )}
      </svg>

      {/* Label text */}
      <div
        style={{
          position: 'absolute',
          left: bracketWidth + 8,
          top: (yBottom - yTop) / 2 - 8,
          fontFamily: FONTS.sans,
          fontSize: 11,
          color,
          opacity: textOpacity + pulseOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        {text}
      </div>
    </div>
  );
};
