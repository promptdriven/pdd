import React from 'react';
import { AbsoluteFill, useCurrentFrame, Easing, interpolate } from 'remotion';
import { CANVAS, TRIANGLE, NODES, TIMING } from './constants';
import TriangleEdge from './TriangleEdge';
import NodeCircle from './NodeCircle';
import CodeLines from './CodeLines';

export const defaultClosing04PddTriangleProps = {};

export const Closing04PddTriangle: React.FC = () => {
  const frame = useCurrentFrame();

  // Background opacity fade-in (frames 0-30)
  const bgOpacity = interpolate(frame, [0, TIMING.BG_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Radial glow opacity (fades in with background)
  const glowOpacity = interpolate(frame, [0, TIMING.BG_END], [0, CANVAS.GLOW_OPACITY], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.BG_COLOR,
        opacity: bgOpacity,
      }}
    >
      {/* Radial glow */}
      <div
        style={{
          position: 'absolute',
          left: CANVAS.CENTER.x - CANVAS.GLOW_RADIUS,
          top: CANVAS.CENTER.y - CANVAS.GLOW_RADIUS,
          width: CANVAS.GLOW_RADIUS * 2,
          height: CANVAS.GLOW_RADIUS * 2,
          borderRadius: '50%',
          background: `radial-gradient(circle, ${CANVAS.GLOW_COLOR} 0%, transparent 70%)`,
          opacity: glowOpacity,
        }}
      />

      {/* Triangle edges — draw sequentially */}
      {/* Edge 1: PROMPT (top) → TESTS (bottom-left) */}
      <TriangleEdge
        fromX={NODES.PROMPT.cx}
        fromY={NODES.PROMPT.cy}
        toX={NODES.TESTS.cx}
        toY={NODES.TESTS.cy}
        color={TRIANGLE.EDGE_COLOR}
        strokeOpacity={TRIANGLE.EDGE_OPACITY}
        strokeWidth={TRIANGLE.EDGE_WIDTH}
        glowBlur={TRIANGLE.EDGE_GLOW_BLUR}
        glowOpacity={TRIANGLE.EDGE_GLOW_OPACITY}
        startFrame={TIMING.EDGE_1_START}
        drawDuration={TIMING.EDGE_DRAW_DURATION}
      />

      {/* Edge 2: TESTS (bottom-left) → GROUNDING (bottom-right) */}
      <TriangleEdge
        fromX={NODES.TESTS.cx}
        fromY={NODES.TESTS.cy}
        toX={NODES.GROUNDING.cx}
        toY={NODES.GROUNDING.cy}
        color={TRIANGLE.EDGE_COLOR}
        strokeOpacity={TRIANGLE.EDGE_OPACITY}
        strokeWidth={TRIANGLE.EDGE_WIDTH}
        glowBlur={TRIANGLE.EDGE_GLOW_BLUR}
        glowOpacity={TRIANGLE.EDGE_GLOW_OPACITY}
        startFrame={TIMING.EDGE_2_START}
        drawDuration={TIMING.EDGE_DRAW_DURATION}
      />

      {/* Edge 3: GROUNDING (bottom-right) → PROMPT (top) */}
      <TriangleEdge
        fromX={NODES.GROUNDING.cx}
        fromY={NODES.GROUNDING.cy}
        toX={NODES.PROMPT.cx}
        toY={NODES.PROMPT.cy}
        color={TRIANGLE.EDGE_COLOR}
        strokeOpacity={TRIANGLE.EDGE_OPACITY}
        strokeWidth={TRIANGLE.EDGE_WIDTH}
        glowBlur={TRIANGLE.EDGE_GLOW_BLUR}
        glowOpacity={TRIANGLE.EDGE_GLOW_OPACITY}
        startFrame={TIMING.EDGE_3_START}
        drawDuration={TIMING.EDGE_DRAW_DURATION}
      />

      {/* PROMPT node — top */}
      <NodeCircle
        cx={NODES.PROMPT.cx}
        cy={NODES.PROMPT.cy}
        color={NODES.PROMPT.color}
        label={NODES.PROMPT.label}
        labelY={NODES.PROMPT.labelY}
        descriptor={NODES.PROMPT.descriptor}
        descriptorY={NODES.PROMPT.descriptorY}
        nodeStartFrame={TIMING.PROMPT_NODE_START}
        descriptorStartFrame={TIMING.DESCRIPTOR_PROMPT_START}
        pulseStartFrame={TIMING.PULSE_START}
      />

      {/* TESTS node — bottom-left */}
      <NodeCircle
        cx={NODES.TESTS.cx}
        cy={NODES.TESTS.cy}
        color={NODES.TESTS.color}
        label={NODES.TESTS.label}
        labelY={NODES.TESTS.labelY}
        descriptor={NODES.TESTS.descriptor}
        descriptorY={NODES.TESTS.descriptorY}
        nodeStartFrame={TIMING.TESTS_NODE_START}
        descriptorStartFrame={TIMING.DESCRIPTOR_TESTS_START}
        pulseStartFrame={TIMING.PULSE_START}
      />

      {/* GROUNDING node — bottom-right */}
      <NodeCircle
        cx={NODES.GROUNDING.cx}
        cy={NODES.GROUNDING.cy}
        color={NODES.GROUNDING.color}
        label={NODES.GROUNDING.label}
        labelY={NODES.GROUNDING.labelY}
        descriptor={NODES.GROUNDING.descriptor}
        descriptorY={NODES.GROUNDING.descriptorY}
        nodeStartFrame={TIMING.GROUNDING_NODE_START}
        descriptorStartFrame={TIMING.DESCRIPTOR_GROUNDING_START}
        pulseStartFrame={TIMING.PULSE_START}
      />

      {/* Generated code lines at center */}
      <CodeLines />
    </AbsoluteFill>
  );
};

export default Closing04PddTriangle;
