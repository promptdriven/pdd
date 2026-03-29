import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { NODE_FILL, ROOT_BORDER_RADIUS } from './constants';

interface FlowNodeProps {
  text: string;
  borderColor: string;
  textColor: string;
  x: number;
  y: number;
  width: number;
  height: number;
  fadeStartFrame: number;
  fadeDuration: number;
  fontSize?: number;
  fontWeight?: number;
}

export const FlowNode: React.FC<FlowNodeProps> = ({
  text,
  borderColor,
  textColor,
  x,
  y,
  width,
  height,
  fadeStartFrame,
  fadeDuration,
  fontSize = 14,
  fontWeight = 600,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeStartFrame, fadeStartFrame + fadeDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const scale = interpolate(
    frame,
    [fadeStartFrame, fadeStartFrame + fadeDuration],
    [0.85, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: x - width / 2,
        top: y - height / 2,
        width,
        height,
        backgroundColor: NODE_FILL,
        border: `2px solid ${borderColor}`,
        borderRadius: ROOT_BORDER_RADIUS,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        opacity,
        transform: `scale(${scale})`,
      }}
    >
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize,
          fontWeight,
          color: textColor,
          lineHeight: 1,
        }}
      >
        {text}
      </span>
    </div>
  );
};
