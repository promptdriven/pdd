import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { LABEL_FADE_IN_FRAMES } from './constants';

interface FlowLabelProps {
  text: string;
  color: string;
  x: number;
  y: number;
  /** Local start frame (relative to the Sequence this lives in) */
  componentLabel?: string;
}

export const FlowLabel: React.FC<FlowLabelProps> = ({
  text,
  color,
  x,
  y,
  componentLabel,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, LABEL_FADE_IN_FRAMES], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const translateX = interpolate(frame, [0, LABEL_FADE_IN_FRAMES], [20, 0], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        opacity,
        transform: `translateX(${translateX}px)`,
        display: 'flex',
        flexDirection: 'column',
        gap: 2,
      }}
    >
      {/* Connector line */}
      <div
        style={{
          position: 'absolute',
          left: -40,
          top: '50%',
          width: 36,
          height: 2,
          backgroundColor: color,
          opacity: 0.5,
          transform: 'translateY(-50%)',
        }}
      />
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color,
          lineHeight: 1.2,
          whiteSpace: 'nowrap',
        }}
      >
        {text}
      </span>
      {componentLabel && (
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 11,
            fontWeight: 400,
            color,
            opacity: 0.6,
            lineHeight: 1.2,
            whiteSpace: 'nowrap',
          }}
        >
          {componentLabel}
        </span>
      )}
    </div>
  );
};
