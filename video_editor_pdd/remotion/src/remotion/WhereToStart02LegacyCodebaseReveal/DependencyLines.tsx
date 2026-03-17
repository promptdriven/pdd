import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  EDGE_COLOR,
  EDGE_OPACITY,
  type BlockDef,
  type EdgeDef,
} from './constants';

interface DependencyLinesProps {
  blocks: BlockDef[];
  edges: EdgeDef[];
}

export const DependencyLines: React.FC<DependencyLinesProps> = ({ blocks, edges }) => {
  const frame = useCurrentFrame();

  // Edges draw in from frame 5 to frame 30 (staggered, 25-frame draw duration)
  const drawProgress = interpolate(
    frame,
    [5, 30],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Full density reached by frame 60
  const densityProgress = interpolate(
    frame,
    [30, 60],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const blockMap = new Map(blocks.map((b) => [b.id, b]));

  return (
    <svg
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        pointerEvents: 'none',
      }}
    >
      {edges.map((edge, i) => {
        const fromBlock = blockMap.get(edge.from);
        const toBlock = blockMap.get(edge.to);
        if (!fromBlock || !toBlock) return null;

        // Center points of each block
        const x1 = fromBlock.x + fromBlock.w / 2;
        const y1 = fromBlock.y + fromBlock.h / 2;
        const x2 = toBlock.x + toBlock.w / 2;
        const y2 = toBlock.y + toBlock.h / 2;

        // Stagger each edge's appearance
        const edgeStagger = (i / edges.length);
        const edgeDrawn = drawProgress > edgeStagger ? 1 : 0;

        // Line length for dash animation
        const length = Math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2);

        // Animate the stroke-dashoffset
        const localProgress = interpolate(
          drawProgress,
          [edgeStagger, Math.min(edgeStagger + 0.3, 1)],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        const dashOffset = length * (1 - localProgress);

        // Later edges get lower opacity until full density is reached
        const isLateEdge = i > edges.length * 0.6;
        const opacity = isLateEdge
          ? EDGE_OPACITY * densityProgress
          : EDGE_OPACITY * Math.min(drawProgress / Math.max(edgeStagger + 0.1, 0.01), 1);

        return (
          <line
            key={i}
            x1={x1}
            y1={y1}
            x2={x2}
            y2={y2}
            stroke={EDGE_COLOR}
            strokeWidth={1}
            strokeOpacity={opacity}
            strokeDasharray={length}
            strokeDashoffset={dashOffset}
          />
        );
      })}
    </svg>
  );
};
