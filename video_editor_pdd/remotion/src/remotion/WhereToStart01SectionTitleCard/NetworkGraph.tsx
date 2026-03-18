import React from 'react';
import { AbsoluteFill, useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  TOPOLOGY_NODES,
  TOPOLOGY_EDGES,
  HIGHLIGHT_NODE_INDEX,
  OPACITIES,
  TIMING,
  COLORS,
  CANVAS,
} from './constants';

export const NetworkGraph: React.FC = () => {
  const frame = useCurrentFrame();
  const totalNodes = TOPOLOGY_NODES.length;

  // Pulse cycle for highlighted node
  const pulsePhase = (frame % TIMING.nodePulsePeriod) / TIMING.nodePulsePeriod;
  const pulseOpacity = interpolate(
    Math.sin(pulsePhase * Math.PI * 2),
    [-1, 1],
    [OPACITIES.highlightPulseMin, OPACITIES.highlightPulseMax]
  );

  // Edge draw progress (starts after all nodes have begun appearing)
  const edgeStart = totalNodes * TIMING.topologyDraw.nodeStagger;
  const edgeProgress = interpolate(
    frame,
    [edgeStart, edgeStart + TIMING.topologyDraw.edgeDrawDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) }
  );

  return (
    <AbsoluteFill>
      <svg width={CANVAS.width} height={CANVAS.height}>
        {/* Edges */}
        {TOPOLOGY_EDGES.map(([from, to], i) => {
          const n1 = TOPOLOGY_NODES[from];
          const n2 = TOPOLOGY_NODES[to];
          // Stagger each edge slightly across the draw duration
          const edgeFrac = i / TOPOLOGY_EDGES.length;
          const thisEdgeProgress = interpolate(
            edgeProgress,
            [edgeFrac * 0.5, edgeFrac * 0.5 + 0.5],
            [0, 1],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );

          if (thisEdgeProgress <= 0) return null;

          const dx = n2.x - n1.x;
          const dy = n2.y - n1.y;
          const endX = n1.x + dx * thisEdgeProgress;
          const endY = n1.y + dy * thisEdgeProgress;

          return (
            <line
              key={`e-${i}`}
              x1={n1.x}
              y1={n1.y}
              x2={endX}
              y2={endY}
              stroke={COLORS.nodeColor}
              strokeWidth={1}
              opacity={OPACITIES.edgeBase}
            />
          );
        })}

        {/* Nodes */}
        {TOPOLOGY_NODES.map((node, i) => {
          const nodeAppearFrame = i * TIMING.topologyDraw.nodeStagger;
          const nodeOpacity = interpolate(
            frame,
            [nodeAppearFrame, nodeAppearFrame + 10],
            [0, 1],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(2)) }
          );

          if (nodeOpacity <= 0) return null;

          const isHighlight = i === HIGHLIGHT_NODE_INDEX;
          const baseOpacity = isHighlight ? pulseOpacity : OPACITIES.nodeBase;

          return (
            <React.Fragment key={`n-${i}`}>
              {/* Glow for highlight node */}
              {isHighlight && (
                <circle
                  cx={node.x}
                  cy={node.y}
                  r={18}
                  fill={COLORS.highlightNode}
                  opacity={OPACITIES.highlightGlow * nodeOpacity}
                  filter="url(#glowFilter)"
                />
              )}
              <circle
                cx={node.x}
                cy={node.y}
                r={6}
                fill={isHighlight ? COLORS.highlightNode : COLORS.nodeColor}
                opacity={baseOpacity * nodeOpacity}
              />
            </React.Fragment>
          );
        })}

        {/* SVG filter for Gaussian blur glow */}
        <defs>
          <filter id="glowFilter" x="-100%" y="-100%" width="300%" height="300%">
            <feGaussianBlur stdDeviation="12" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>
      </svg>
    </AbsoluteFill>
  );
};
