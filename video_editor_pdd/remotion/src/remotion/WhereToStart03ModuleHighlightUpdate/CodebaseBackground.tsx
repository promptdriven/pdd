import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CODEBASE_BLOCKS,
  CODEBASE_EDGES,
  BLOCK_FILL,
  EDGE_COLOR,
  MODULE_POS,
  MODULE_SIZE,
  SELECTION_BLUE,
} from './constants';

/**
 * Renders the dimmed codebase graph with blocks and dependency edges.
 * The selected module (index 5) gets a pulsing blue glow.
 */
export const CodebaseBackground: React.FC = () => {
  const frame = useCurrentFrame();

  // Entire codebase dims to 0.3 over frames 0-20
  const dimOpacity = interpolate(frame, [0, 20], [0.6, 0.3], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Pulsing glow for selected module — sine cycle of 30 frames
  const pulsePhase = (frame % 30) / 30;
  const pulseVal = 0.5 + 0.5 * Math.sin(pulsePhase * Math.PI * 2);
  const glowOpacity = 0.08 + pulseVal * 0.08; // 0.08 - 0.16
  const borderOpacity = 0.3 + pulseVal * 0.2; // 0.3 - 0.5

  return (
    <div style={{ position: 'absolute', inset: 0 }}>
      {/* Edges */}
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0, opacity: dimOpacity }}
      >
        {CODEBASE_EDGES.map(([from, to], idx) => {
          const a = CODEBASE_BLOCKS[from];
          const b = CODEBASE_BLOCKS[to];
          return (
            <line
              key={idx}
              x1={a.x + a.w / 2}
              y1={a.y + a.h / 2}
              x2={b.x + b.w / 2}
              y2={b.y + b.h / 2}
              stroke={EDGE_COLOR}
              strokeWidth={1}
              strokeOpacity={0.08}
            />
          );
        })}
      </svg>

      {/* Blocks (non-selected) */}
      {CODEBASE_BLOCKS.map((block, idx) => {
        const isSelected = idx === 5;
        if (isSelected) return null;
        return (
          <div
            key={idx}
            style={{
              position: 'absolute',
              left: block.x,
              top: block.y,
              width: block.w,
              height: block.h,
              backgroundColor: BLOCK_FILL,
              borderRadius: 4,
              opacity: dimOpacity,
              border: `1px solid ${EDGE_COLOR}`,
            }}
          />
        );
      })}

      {/* Selected module block with glow */}
      <div
        style={{
          position: 'absolute',
          left: MODULE_POS.x,
          top: MODULE_POS.y,
          width: MODULE_SIZE.w,
          height: MODULE_SIZE.h,
          backgroundColor: BLOCK_FILL,
          borderRadius: 4,
          border: `2px solid rgba(74, 144, 217, ${borderOpacity})`,
          boxShadow: `0 0 20px rgba(74, 144, 217, ${glowOpacity}), inset 0 0 10px rgba(74, 144, 217, 0.05)`,
        }}
      >
        {/* Inner selection highlight */}
        <div
          style={{
            position: 'absolute',
            inset: 0,
            borderRadius: 3,
            backgroundColor: SELECTION_BLUE,
            opacity: 0.15,
          }}
        />
        {/* Fake code lines inside the block */}
        <div style={{ padding: '8px 10px', display: 'flex', flexDirection: 'column', gap: 3 }}>
          {[0.7, 0.5, 0.85, 0.6, 0.4].map((w, i) => (
            <div
              key={i}
              style={{
                height: 3,
                width: `${w * 100}%`,
                backgroundColor: '#64748B',
                opacity: 0.4,
                borderRadius: 1,
              }}
            />
          ))}
        </div>
      </div>
    </div>
  );
};

export default CodebaseBackground;
