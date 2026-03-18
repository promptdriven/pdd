// AnimatedNode.tsx — Pulsing triangle node with glow
import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  NODE_RADIUS_START,
  NODE_RADIUS_END,
  NODE_GROW_DURATION,
  NODE_GLOW_RADIUS,
  PULSE_MIN,
  PULSE_MAX,
  PULSE_PERIOD,
  GLOW_APPEAR_DURATION,
} from './constants';

interface AnimatedNodeProps {
  center: [number, number];
  fillColor: string;
  glowColor: string;
  glowOpacity: number;
}

export const AnimatedNode: React.FC<AnimatedNodeProps> = ({
  center,
  fillColor,
  glowColor,
  glowOpacity,
}) => {
  const frame = useCurrentFrame();
  const [cx, cy] = center;

  // Node scale: 12 → 22px over 18 frames with easeOut(back(1.3))
  // Remotion doesn't have Easing.back, so we simulate a slight overshoot
  // using a custom approach: interpolate with overshoot via poly + extra range
  const growProgress = interpolate(frame, [0, NODE_GROW_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(3)),
  });

  // Simulate back easing overshoot: overshoot to ~24 then settle to 22
  const overshootRadius = interpolate(
    frame,
    [0, NODE_GROW_DURATION * 0.7, NODE_GROW_DURATION],
    [NODE_RADIUS_START, NODE_RADIUS_END + 3, NODE_RADIUS_END],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)),
    }
  );

  // Continuous pulse after grow is done: 22 → 24 → 22 over 90 frames
  const pulsePhase = ((frame - NODE_GROW_DURATION) % PULSE_PERIOD) / PULSE_PERIOD;
  const pulseValue =
    PULSE_MIN +
    (PULSE_MAX - PULSE_MIN) * 0.5 * (1 - Math.cos(2 * Math.PI * pulsePhase));

  const baseRadius = frame < NODE_GROW_DURATION ? overshootRadius : pulseValue;

  // Glow opacity fades in over GLOW_APPEAR_DURATION
  const glowOpacityAnimated = interpolate(
    frame,
    [0, GLOW_APPEAR_DURATION],
    [0, glowOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)),
    }
  );

  // Node fill opacity: brightens with growth
  const fillOpacity = interpolate(frame, [0, NODE_GROW_DURATION], [0.3, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(3)),
  });

  const size = baseRadius * 2 + NODE_GLOW_RADIUS * 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: cx - size / 2,
        top: cy - size / 2,
        width: size,
        height: size,
        pointerEvents: 'none',
      }}
    >
      <svg
        width={size}
        height={size}
        viewBox={`0 0 ${size} ${size}`}
        style={{ overflow: 'visible' }}
      >
        <defs>
          <radialGradient id={`glow-${cx}-${cy}`}>
            <stop offset="0%" stopColor={glowColor} stopOpacity={glowOpacityAnimated} />
            <stop offset="100%" stopColor={glowColor} stopOpacity={0} />
          </radialGradient>
        </defs>
        {/* Outer glow */}
        <circle
          cx={size / 2}
          cy={size / 2}
          r={NODE_GLOW_RADIUS}
          fill={`url(#glow-${cx}-${cy})`}
        />
        {/* Node fill */}
        <circle
          cx={size / 2}
          cy={size / 2}
          r={baseRadius}
          fill={fillColor}
          opacity={fillOpacity}
        />
      </svg>
    </div>
  );
};

export default AnimatedNode;
