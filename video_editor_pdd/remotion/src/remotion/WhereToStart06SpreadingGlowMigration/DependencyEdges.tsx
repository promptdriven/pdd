import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  MODULES,
  EDGES,
  EDGE_UNCONVERTED,
  EDGE_CONVERTED,
  CANVAS_W,
  CANVAS_H,
} from './constants';

interface DependencyEdgesProps {
  convertedModuleIds: Set<number>;
  /** Frame at which each module became fully converted (for edge transition timing) */
  conversionCompletionFrames: Map<number, number>;
}

const EDGE_TRANSITION_DURATION = 15;

export const DependencyEdges: React.FC<DependencyEdgesProps> = ({
  convertedModuleIds,
  conversionCompletionFrames,
}) => {
  const frame = useCurrentFrame();

  return (
    <svg
      width={CANVAS_W}
      height={CANVAS_H}
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      {EDGES.map(([fromId, toId], i) => {
        const fromMod = MODULES[fromId];
        const toMod = MODULES[toId];
        if (!fromMod || !toMod) return null;

        const fromConverted = convertedModuleIds.has(fromId);
        const toConverted = convertedModuleIds.has(toId);
        const bothConverted = fromConverted && toConverted;

        // Determine edge transition progress
        let edgeProgress = 0;
        if (bothConverted) {
          // Use the later of the two modules' completion frames
          const fromComplete = conversionCompletionFrames.get(fromId) ?? 0;
          const toComplete = conversionCompletionFrames.get(toId) ?? 0;
          const laterFrame = Math.max(fromComplete, toComplete);

          edgeProgress = interpolate(
            frame,
            [laterFrame, laterFrame + EDGE_TRANSITION_DURATION],
            [0, 1],
            {
              easing: Easing.out(Easing.quad),
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
            },
          );
        }

        const color = bothConverted && edgeProgress > 0
          ? EDGE_CONVERTED.color
          : EDGE_UNCONVERTED.color;

        const opacity = bothConverted
          ? EDGE_UNCONVERTED.opacity + edgeProgress * (EDGE_CONVERTED.opacity - EDGE_UNCONVERTED.opacity)
          : EDGE_UNCONVERTED.opacity;

        const strokeWidth = bothConverted
          ? EDGE_UNCONVERTED.width + edgeProgress * (EDGE_CONVERTED.width - EDGE_UNCONVERTED.width)
          : EDGE_UNCONVERTED.width;

        return (
          <line
            key={i}
            x1={fromMod.x}
            y1={fromMod.y}
            x2={toMod.x}
            y2={toMod.y}
            stroke={color}
            strokeOpacity={opacity}
            strokeWidth={strokeWidth}
          />
        );
      })}
    </svg>
  );
};
