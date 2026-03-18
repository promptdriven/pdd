import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  CODEBASE_BLOCKS,
  CODEBASE_EDGES,
  BLOCK_FILL,
  EDGE_COLOR,
  BLUE_ACCENT,
  TEXT_LIGHT,
  MODULE_X,
  MODULE_Y,
  MODULE_W,
  MODULE_H,
} from './constants';

const CodebaseBackground: React.FC = () => {
  const frame = useCurrentFrame();

  // Codebase dims to 0.3 opacity over first 20 frames
  const codebaseOpacity = interpolate(frame, [0, 20], [0.6, 0.3], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Selection glow pulse: easeInOut sine on 30-frame cycle
  const glowPhase = (frame % 30) / 30;
  const glowIntensity = interpolate(
    Math.sin(glowPhase * Math.PI * 2),
    [-1, 1],
    [0.08, 0.2],
  );

  // Label fade-in from frame 20
  const labelOpacity = interpolate(frame, [20, 35], [0, 0.7], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <>
      {/* Dimmed codebase edges */}
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0, opacity: codebaseOpacity }}
      >
        {CODEBASE_EDGES.map(([fromIdx, toIdx], i) => {
          const from = CODEBASE_BLOCKS[fromIdx];
          const to = CODEBASE_BLOCKS[toIdx];
          if (!from || !to) return null;
          return (
            <line
              key={i}
              x1={from.x + from.w / 2}
              y1={from.y + from.h / 2}
              x2={to.x + to.w / 2}
              y2={to.y + to.h / 2}
              stroke={EDGE_COLOR}
              strokeWidth={1}
              opacity={0.08}
            />
          );
        })}
      </svg>

      {/* Dimmed codebase blocks (excluding the selected module at index 3) */}
      {CODEBASE_BLOCKS.map((block, i) => {
        if (i === 3) return null; // selected module handled separately
        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: block.x,
              top: block.y,
              width: block.w,
              height: block.h,
              backgroundColor: BLOCK_FILL,
              borderRadius: 4,
              border: `1px solid ${EDGE_COLOR}`,
              opacity: codebaseOpacity,
            }}
          />
        );
      })}

      {/* Selected module block with glow */}
      <div
        style={{
          position: 'absolute',
          left: MODULE_X,
          top: MODULE_Y,
          width: MODULE_W,
          height: MODULE_H,
          backgroundColor: BLOCK_FILL,
          borderRadius: 4,
          border: `2px solid ${BLUE_ACCENT}`,
          borderColor: `rgba(74, 144, 217, 0.4)`,
          boxShadow: `0 0 20px rgba(74, 144, 217, ${glowIntensity}), inset 0 0 15px rgba(74, 144, 217, 0.15)`,
        }}
      >
        {/* Simulated code lines inside the module block */}
        <div style={{ padding: '8px 10px', display: 'flex', flexDirection: 'column', gap: 3 }}>
          {[0.7, 0.5, 0.8, 0.4, 0.6].map((width, i) => (
            <div
              key={i}
              style={{
                width: `${width * 100}%`,
                height: 3,
                backgroundColor: BLUE_ACCENT,
                opacity: 0.25,
                borderRadius: 1,
              }}
            />
          ))}
        </div>
      </div>

      {/* Module label: auth_handler.py */}
      <div
        style={{
          position: 'absolute',
          left: MODULE_X + MODULE_W / 2,
          top: MODULE_Y + MODULE_H + 8,
          transform: 'translateX(-50%)',
          fontFamily: '"JetBrains Mono", monospace',
          fontSize: 11,
          color: TEXT_LIGHT,
          opacity: labelOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        auth_handler.py
      </div>
    </>
  );
};

export default CodebaseBackground;
