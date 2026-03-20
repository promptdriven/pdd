import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COUNTER_FONT_SIZE,
  COUNTER_SUFFIX_FONT_SIZE,
  COUNTER_SUFFIX_OPACITY,
  COUNTER_START,
  COUNTER_DURATION,
} from './constants';

interface AnimatedCounterProps {
  from: number;
  to: number;
  suffix: string;
  color: string;
  counterOpacity: number;
  align: 'left' | 'right';
  x: number;
  y: number;
}

export const AnimatedCounter: React.FC<AnimatedCounterProps> = ({
  from,
  to,
  suffix,
  color,
  counterOpacity,
  align,
  x,
  y,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [COUNTER_START, COUNTER_START + COUNTER_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.exp),
    }
  );

  const fadeIn = interpolate(
    frame,
    [COUNTER_START, COUNTER_START + 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const currentValue = Math.round(from + (to - from) * progress);
  const formattedValue = currentValue.toLocaleString();

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        opacity: fadeIn,
        textAlign: align,
        whiteSpace: 'nowrap',
      }}
    >
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontWeight: 700,
          fontSize: COUNTER_FONT_SIZE,
          color,
          opacity: counterOpacity,
        }}
      >
        {formattedValue}
      </span>
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontWeight: 400,
          fontSize: COUNTER_SUFFIX_FONT_SIZE,
          color,
          opacity: COUNTER_SUFFIX_OPACITY,
          marginLeft: 4,
        }}
      >
        {suffix}
      </span>
    </div>
  );
};

export default AnimatedCounter;
