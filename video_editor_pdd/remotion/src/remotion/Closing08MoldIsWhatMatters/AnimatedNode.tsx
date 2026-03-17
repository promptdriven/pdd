import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  NODE_RADIUS_START,
  NODE_RADIUS_END,
  NODE_GROW_DURATION,
  NODE_GLOW_RADIUS,
  NODE_GLOW_OPACITY,
  NODE_PULSE_MIN,
  NODE_PULSE_MAX,
  NODE_PULSE_PERIOD,
  GLOW_APPEAR_DURATION,
} from './constants';

interface AnimatedNodeProps {
  cx: number;
  cy: number;
  fillColor: string;
  glowColor: string;
}

export const AnimatedNode: React.FC<AnimatedNodeProps> = ({
  cx,
  cy,
  fillColor,
  glowColor,
}) => {
  const frame = useCurrentFrame();

  // Node grows from ghost size to full size with back easing
  const growProgress = interpolate(frame, [0, NODE_GROW_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.back(1.3)),
  });

  const baseRadius = NODE_RADIUS_START + (NODE_RADIUS_END - NODE_RADIUS_START) * growProgress;

  // After grow completes, add a gentle synchronized pulse
  const pulsePhase = ((frame % NODE_PULSE_PERIOD) / NODE_PULSE_PERIOD) * Math.PI * 2;
  const pulseAmount = frame > NODE_GROW_DURATION
    ? (Math.sin(pulsePhase) + 1) / 2 // 0..1
    : 0;
  const pulseRadius = NODE_PULSE_MIN + (NODE_PULSE_MAX - NODE_PULSE_MIN) * pulseAmount;
  const radius = frame > NODE_GROW_DURATION ? pulseRadius : baseRadius;

  // Glow fades in
  const glowOpacity = interpolate(frame, [0, GLOW_APPEAR_DURATION], [0, NODE_GLOW_OPACITY], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Node color opacity (brightens from dim)
  const colorOpacity = interpolate(frame, [0, NODE_GROW_DURATION], [0.3, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  const filterId = `node-glow-${cx}-${cy}`;

  return (
    <g>
      {/* Outer glow */}
      <defs>
        <filter id={filterId} x="-200%" y="-200%" width="500%" height="500%">
          <feGaussianBlur in="SourceGraphic" stdDeviation={NODE_GLOW_RADIUS / 2} />
        </filter>
      </defs>
      <circle
        cx={cx}
        cy={cy}
        r={radius + 8}
        fill={glowColor}
        opacity={glowOpacity}
        filter={`url(#${filterId})`}
      />
      {/* Main node */}
      <circle
        cx={cx}
        cy={cy}
        r={radius}
        fill={fillColor}
        opacity={colorOpacity}
      />
    </g>
  );
};
