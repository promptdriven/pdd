/**
 * WorkflowTitle - Title for each workflow side
 */

import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface WorkflowTitleProps {
  text: string;
  color: string;
  x: number;
  y: number;
  startFrame?: number;
}

export const WorkflowTitle: React.FC<WorkflowTitleProps> = ({
  text,
  color,
  x,
  y,
  startFrame = 0,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame - startFrame,
    [0, 15],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.ease),
    }
  );

  const translateY = interpolate(
    frame - startFrame,
    [0, 15],
    [20, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.ease),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        transform: `translate(-50%, 0) translateY(${translateY}px)`,
        opacity,
        fontFamily: 'Inter, sans-serif',
        fontWeight: 700,
        fontSize: 36,
        color,
        textAlign: 'center',
      }}
    >
      {text}
    </div>
  );
};
