import React from 'react';
import { AbsoluteFill, useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  CANVAS,
  COLORS,
  TOPOLOGY,
  TIMING,
  NODES,
  EDGES,
} from './constants';

export const NetworkGraph: React.FC = () => {
  const frame = useCurrentFrame();

  // Node stagger: each node appears 1 frame apart starting from frame 0 (relative to Sequence)
  const nodeElements = NODES.map((node, i) => {
    const nodeAppearFrame = i * TIMING.TOPOLOGY_NODE_STAGGER;
    const nodeOpacity = interpolate(frame, [nodeAppearFrame, nodeAppearFrame + 10], [0, 1], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    });

    const isHighlight = i === TOPOLOGY.HIGHLIGHT_INDEX;

    if (isHighlight) {
      // Pulsing node
      const pulsePhase = ((frame - 90 + TOPOLOGY.PULSE_PERIOD) % TOPOLOGY.PULSE_PERIOD) / TOPOLOGY.PULSE_PERIOD;
      const pulseOpacity = interpolate(
        Math.sin(pulsePhase * Math.PI * 2),
        [-1, 1],
        [TOPOLOGY.PULSE_MIN, TOPOLOGY.PULSE_MAX],
      );
      const currentOpacity = frame >= 90 ? pulseOpacity : TOPOLOGY.HIGHLIGHT_OPACITY;

      return (
        <g key={i} opacity={nodeOpacity}>
          {/* Glow */}
          <circle
            cx={node.x}
            cy={node.y}
            r={TOPOLOGY.NODE_RADIUS + TOPOLOGY.GLOW_BLUR}
            fill={COLORS.HIGHLIGHT}
            opacity={TOPOLOGY.GLOW_OPACITY * nodeOpacity}
            filter="url(#highlightGlow)"
          />
          {/* Core node */}
          <circle
            cx={node.x}
            cy={node.y}
            r={TOPOLOGY.NODE_RADIUS}
            fill={COLORS.HIGHLIGHT}
            opacity={currentOpacity}
          />
        </g>
      );
    }

    return (
      <circle
        key={i}
        cx={node.x}
        cy={node.y}
        r={TOPOLOGY.NODE_RADIUS}
        fill={COLORS.NODE}
        opacity={TOPOLOGY.NODE_OPACITY * nodeOpacity}
      />
    );
  });

  // Edge draw animation: all edges draw over TOPOLOGY_EDGE_DRAW frames
  // starting after all nodes have appeared
  const edgeStartFrame = NODES.length * TIMING.TOPOLOGY_NODE_STAGGER;
  const edgeElements = EDGES.map(([a, b], i) => {
    const n1 = NODES[a];
    const n2 = NODES[b];
    const edgeDelay = (i / EDGES.length) * TIMING.TOPOLOGY_EDGE_DRAW * 0.5;
    const drawProgress = interpolate(
      frame,
      [edgeStartFrame + edgeDelay, edgeStartFrame + edgeDelay + TIMING.TOPOLOGY_EDGE_DRAW],
      [0, 1],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.cubic),
      },
    );

    if (drawProgress <= 0) return null;

    const x2 = n1.x + (n2.x - n1.x) * drawProgress;
    const y2 = n1.y + (n2.y - n1.y) * drawProgress;

    // Check if either end is the highlight node
    const isHighlightEdge = a === TOPOLOGY.HIGHLIGHT_INDEX || b === TOPOLOGY.HIGHLIGHT_INDEX;

    return (
      <line
        key={`e-${i}`}
        x1={n1.x}
        y1={n1.y}
        x2={x2}
        y2={y2}
        stroke={isHighlightEdge ? COLORS.HIGHLIGHT : COLORS.NODE}
        strokeWidth={1}
        opacity={isHighlightEdge ? TOPOLOGY.EDGE_OPACITY * 2 : TOPOLOGY.EDGE_OPACITY}
      />
    );
  });

  return (
    <AbsoluteFill>
      <svg
        width={CANVAS.WIDTH}
        height={CANVAS.HEIGHT}
        viewBox={`0 0 ${CANVAS.WIDTH} ${CANVAS.HEIGHT}`}
      >
        <defs>
          <filter id="highlightGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur in="SourceGraphic" stdDeviation={TOPOLOGY.GLOW_BLUR} />
          </filter>
        </defs>
        {edgeElements}
        {nodeElements}
      </svg>
    </AbsoluteFill>
  );
};
