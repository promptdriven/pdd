import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  NODE_RADIUS,
  NODE_PULSE_MIN,
  NODE_PULSE_MAX,
  NODE_PULSE_PERIOD,
  TIMING,
} from './constants';

interface NodeData {
  id: string;
  label: string;
  descriptor: string;
  cx: number;
  cy: number;
  color: string;
  labelY: number;
  descriptorY: number;
  labelBelow: boolean;
}

interface NodeCircleProps {
  node: NodeData;
  appearFrame: number;
  descriptorFrame: number;
}

export const NodeCircle: React.FC<NodeCircleProps> = ({
  node,
  appearFrame,
  descriptorFrame,
}) => {
  const frame = useCurrentFrame();

  // Circle scale-in with back easing (bounce overshoot)
  const scaleProgress = interpolate(
    frame,
    [appearFrame, appearFrame + 15],
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
    [appearFrame, appearFrame + 12],
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
    [descriptorFrame, descriptorFrame + 15],
    [0, 0.4],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Pulse after frame 230 — smooth sine oscillation
  const currentRadius = (() => {
    if (frame < TIMING.pulseStart) return NODE_RADIUS;
    const t = (frame - TIMING.pulseStart) / NODE_PULSE_PERIOD;
    const sine = Math.sin(t * Math.PI * 2);
    // Map sine [-1, 1] to [NODE_PULSE_MIN, NODE_PULSE_MAX]
    return NODE_PULSE_MIN + ((sine + 1) / 2) * (NODE_PULSE_MAX - NODE_PULSE_MIN);
  })();

  if (scaleProgress <= 0) return null;

  return (
    <>
      {/* Circle node */}
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <circle
          cx={node.cx}
          cy={node.cy}
          r={currentRadius * scaleProgress}
          fill={node.color}
          stroke={node.color}
          strokeWidth={2}
          strokeOpacity={0.8}
        />
      </svg>

      {/* Label */}
      <div
        style={{
          position: 'absolute',
          left: node.cx,
          top: node.labelY,
          transform: 'translateX(-50%)',
          fontFamily: 'Inter, sans-serif',
          fontSize: 16,
          fontWeight: 700,
          color: node.color,
          opacity: labelOpacity,
          whiteSpace: 'nowrap',
          textAlign: 'center',
        }}
      >
        {node.label}
      </div>

      {/* Descriptor */}
      <div
        style={{
          position: 'absolute',
          left: node.cx,
          top: node.descriptorY,
          transform: 'translateX(-50%)',
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          color: node.color,
          opacity: descriptorOpacity,
          whiteSpace: 'nowrap',
          textAlign: 'center',
        }}
      >
        {node.descriptor}
      </div>
    </>
  );
};
