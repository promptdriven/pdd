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
    <>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          {NODES.map((node, i) => (
            <filter key={i} id={`nodeGlow${i}`} x="-200%" y="-200%" width="500%" height="500%">
              <feGaussianBlur stdDeviation={NODE_GLOW_RADIUS / 2} />
            </filter>
          ))}
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
              {/* Outer glow — large soft halo */}
              <circle
                cx={node.center[0]}
                cy={node.center[1]}
                r={pulseRadius + NODE_GLOW_RADIUS}
                fill={node.glowColor}
                opacity={glowPulseOpacity}
                filter={`url(#nodeGlow${i})`}
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

      {/* Node labels and descriptors (HTML overlay) */}
      {NODES.map((node, i) => {
        const localFrame = Math.max(0, frame - NODE_ANIM_START);

        // Label fades in alongside the node growth
        const labelOpacity = interpolate(
          localFrame,
          [0, NODE_GROW_DURATION],
          [0, 1],
          { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
        );

        // Descriptor fades in slightly after label
        const descriptorOpacity = interpolate(
          localFrame,
          [20, 50],
          [0, 0.4],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
        );

        return (
          <React.Fragment key={`label-${i}`}>
            {/* Label */}
            <div
              style={{
                position: 'absolute',
                left: node.center[0],
                top: node.labelY,
                transform: 'translateX(-50%)',
                fontFamily: 'Inter, sans-serif',
                fontSize: 16,
                fontWeight: 700,
                color: node.glowColor,
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
                left: node.center[0],
                top: node.descriptorY,
                transform: 'translateX(-50%)',
                fontFamily: 'Inter, sans-serif',
                fontSize: 11,
                color: node.glowColor,
                opacity: descriptorOpacity,
                whiteSpace: 'nowrap',
                textAlign: 'center',
              }}
            >
              {node.descriptor}
            </div>
          </React.Fragment>
        );
      })}
    </>
  );
};
