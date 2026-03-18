import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  Easing,
  interpolate,
} from 'remotion';
import { CANVAS, GLOW, NODES, EDGES, TIMING } from './constants';
import { DrawEdge } from './DrawEdge';
import { NodeCircle } from './NodeCircle';
import { CodeLines } from './CodeLines';

export const defaultClosing04PddTriangleProps = {};

export const Closing04PddTriangle: React.FC = () => {
  const frame = useCurrentFrame();

  // Glow fades in over first 30 frames
  const glowOpacity = interpolate(
    frame,
    [0, 30],
    [0, GLOW.opacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.background,
      }}
    >
      {/* Radial glow */}
      <div
        style={{
          position: 'absolute',
          left: GLOW.centerX - GLOW.radius,
          top: GLOW.centerY - GLOW.radius,
          width: GLOW.radius * 2,
          height: GLOW.radius * 2,
          borderRadius: '50%',
          background: `radial-gradient(circle, ${GLOW.color} 0%, transparent 70%)`,
          opacity: glowOpacity,
          pointerEvents: 'none',
        }}
      />

      {/* Triangle edges — drawn sequentially */}
      {EDGES.map((edge, i) => (
        <DrawEdge
          key={i}
          from={edge.from}
          to={edge.to}
          startFrame={edge.startFrame}
        />
      ))}

      {/* Code lines at center (before nodes so nodes render on top) */}
      <CodeLines />

      {/* PROMPT node — top */}
      <NodeCircle
        node={NODES.prompt}
        appearFrame={TIMING.promptNode.start}
        descriptorFrame={TIMING.descriptorPrompt.start}
      />

      {/* TESTS node — bottom-left */}
      <NodeCircle
        node={NODES.tests}
        appearFrame={TIMING.testsNode.start}
        descriptorFrame={TIMING.descriptorTests.start}
      />

      {/* GROUNDING node — bottom-right */}
      <NodeCircle
        node={NODES.grounding}
        appearFrame={TIMING.groundingNode.start}
        descriptorFrame={TIMING.descriptorGrounding.start}
      />
    </AbsoluteFill>
  );
};

export default Closing04PddTriangle;
