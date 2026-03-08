/**
 * ConnectingLines - Lines connecting workflow steps
 */

import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';

interface ConnectingLinesProps {
  x: number;
  startY: number;
  endY: number;
  startFrame: number;
  color: string;
  dashed?: boolean;
  curved?: boolean;
}

export const ConnectingLines: React.FC<ConnectingLinesProps> = ({
  x,
  startY,
  endY,
  startFrame,
  color,
  dashed = false,
  curved = false,
}) => {
  const frame = useCurrentFrame();

  const length = interpolate(
    frame - startFrame,
    [0, 30],
    [0, endY - startY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const opacity = interpolate(
    frame - startFrame,
    [0, 10],
    [0, 0.4],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  if (curved) {
    // SVG curved path for VEO 2 workflow
    const pathLength = Math.abs(endY - startY);
    const strokeDashoffset = interpolate(
      frame - startFrame,
      [0, 30],
      [pathLength, 0],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      }
    );

    return (
      <svg
        style={{
          position: 'absolute',
          left: x - 50,
          top: startY,
          width: 100,
          height: endY - startY,
          overflow: 'visible',
        }}
      >
        <path
          d={`M 50 0 Q 50 ${(endY - startY) / 2}, 50 ${endY - startY}`}
          stroke={color}
          strokeWidth={2}
          fill="none"
          opacity={opacity}
          strokeDasharray={pathLength}
          strokeDashoffset={strokeDashoffset}
        />
      </svg>
    );
  }

  // Straight dashed line for traditional workflow
  return (
    <div
      style={{
        position: 'absolute',
        left: x - 1,
        top: startY,
        width: 2,
        height: length,
        background: color,
        opacity,
        ...(dashed && {
          backgroundImage: `linear-gradient(to bottom, ${color} 8px, transparent 8px)`,
          backgroundSize: '2px 12px',
          background: 'transparent',
          borderLeft: `2px dashed ${color}`,
        }),
      }}
    />
  );
};
