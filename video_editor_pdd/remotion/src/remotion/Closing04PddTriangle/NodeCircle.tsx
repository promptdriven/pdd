import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  NODE_RADIUS,
  NODE_PULSE_MIN,
  NODE_PULSE_MAX,
  NODE_PULSE_PERIOD,
  TIMING,
} from './constants';

interface NodeCircleProps {
  cx: number;
  cy: number;
  color: string;
  label: string;
  labelY: number;
  descriptor: string;
  descriptorY: number;
  nodeStartFrame: number;
  descriptorStartFrame: number;
  pulseStartFrame: number;
}

const NodeCircle: React.FC<NodeCircleProps> = ({
  cx,
  cy,
  color,
  label,
  labelY,
  descriptor,
  descriptorY,
  nodeStartFrame,
  descriptorStartFrame,
  pulseStartFrame,
}) => {
  const frame = useCurrentFrame();

  // Node circle scale-in with back easing (bounce)
  const scaleProgress = interpolate(
    frame,
    [nodeStartFrame, nodeStartFrame + TIMING.NODE_SCALE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.6)),
    },
  );

  // Label fade-in
  const labelOpacity = interpolate(
    frame,
    [nodeStartFrame, nodeStartFrame + TIMING.LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Descriptor fade-in
  const descriptorOpacity = interpolate(
    frame,
    [descriptorStartFrame, descriptorStartFrame + TIMING.DESCRIPTOR_FADE_DURATION],
    [0, 0.4],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Pulse animation (starts at pulseStartFrame, continuous)
  let currentRadius = NODE_RADIUS * scaleProgress;
  if (frame >= pulseStartFrame && scaleProgress >= 1) {
    const pulseFrame = (frame - pulseStartFrame) % NODE_PULSE_PERIOD;
    const pulseProgress = interpolate(
      pulseFrame,
      [0, NODE_PULSE_PERIOD / 2, NODE_PULSE_PERIOD],
      [0, 1, 0],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      },
    );
    currentRadius = NODE_PULSE_MIN + (NODE_PULSE_MAX - NODE_PULSE_MIN) * pulseProgress;
  }

  if (scaleProgress <= 0) return null;

  return (
    <>
      {/* Node circle */}
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <circle
          cx={cx}
          cy={cy}
          r={currentRadius}
          fill={color}
          stroke={color}
          strokeWidth={2}
          strokeOpacity={0.8}
        />
      </svg>

      {/* Label */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          width: 1920,
          top: labelY,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 16,
          fontWeight: 700,
          color,
          opacity: labelOpacity,
          transform: `translateX(${cx - 960}px)`,
        }}
      >
        {label}
      </div>

      {/* Descriptor */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          width: 1920,
          top: descriptorY,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          fontWeight: 400,
          color,
          opacity: descriptorOpacity,
          transform: `translateX(${cx - 960}px)`,
        }}
      >
        {descriptor}
      </div>
    </>
  );
};

export default NodeCircle;
