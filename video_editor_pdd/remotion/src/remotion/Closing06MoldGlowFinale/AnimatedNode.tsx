import React from 'react';
import { useCurrentFrame, interpolate, interpolateColors, Easing } from 'remotion';
import {
  NODE_RADIUS_FROM,
  NODE_RADIUS_TO,
  NODE_GLOW_RADIUS,
  NODE_GLOW_OPACITY,
  NODE_GROW_DURATION,
  NODE_PULSE_PERIOD,
  NODE_ANIM_START,
  NODES,
} from './constants';

export const AnimatedNodes: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="nodeGlow">
          <feGaussianBlur stdDeviation={NODE_GLOW_RADIUS / 3} />
        </filter>
      </defs>

      {NODES.map((node, i) => {
        // Growth animation starts at NODE_ANIM_START
        const localFrame = Math.max(0, frame - NODE_ANIM_START);

        const growProgress = interpolate(
          localFrame,
          [0, NODE_GROW_DURATION],
          [0, 1],
          { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
        );

        const radius = interpolate(growProgress, [0, 1], [NODE_RADIUS_FROM, NODE_RADIUS_TO]);

        const fillColor = interpolateColors(
          growProgress,
          [0, 1],
          [node.fillFrom, node.fillTo]
        );

        // Slow radial pulse every NODE_PULSE_PERIOD frames
        const pulsePhase = ((localFrame % NODE_PULSE_PERIOD) / NODE_PULSE_PERIOD) * Math.PI * 2;
        const pulseScale = 1 + Math.sin(pulsePhase) * 0.08;
        const pulseRadius = radius * pulseScale;

        // Glow fade-in
        const glowOpacity = interpolate(
          localFrame,
          [0, 60],
          [0, NODE_GLOW_OPACITY],
          { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
        );

        // Glow pulse
        const glowPulseOpacity = glowOpacity * (1 + Math.sin(pulsePhase) * 0.3);

        return (
          <g key={i}>
            {/* Outer glow */}
            <circle
              cx={node.center[0]}
              cy={node.center[1]}
              r={pulseRadius + NODE_GLOW_RADIUS * 0.5}
              fill={node.glowColor}
              opacity={glowPulseOpacity}
              filter="url(#nodeGlow)"
            />
            {/* Main fill */}
            <circle
              cx={node.center[0]}
              cy={node.center[1]}
              r={pulseRadius}
              fill={fillColor}
            />
          </g>
        );
      })}
    </svg>
  );
};
