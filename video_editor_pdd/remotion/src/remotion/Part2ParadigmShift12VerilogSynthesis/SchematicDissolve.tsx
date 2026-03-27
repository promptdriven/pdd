import React, { useMemo } from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  SCHEMATIC_LINE_COLOR,
  SCHEMATIC_NODE_COLOR,
  DISSOLVE_START,
  DISSOLVE_END,
} from './constants';

interface SchematicParticle {
  x: number;
  y: number;
  size: number;
  type: 'line' | 'node';
  angle: number;
  velocityX: number;
  velocityY: number;
  rotationSpeed: number;
  width: number;
  height: number;
}

/**
 * Renders a dense hand-drawn schematic that dissolves into particles.
 * Visible from frame 0, dissolves over frames 0–60.
 */
export const SchematicDissolve: React.FC = () => {
  const frame = useCurrentFrame();

  // Generate deterministic schematic elements
  const particles = useMemo<SchematicParticle[]>(() => {
    const items: SchematicParticle[] = [];
    const seed = (i: number) => {
      const s = Math.sin(i * 127.1 + 311.7) * 43758.5453;
      return s - Math.floor(s);
    };

    // Horizontal and vertical lines (schematic wires)
    for (let i = 0; i < 60; i++) {
      const isHorizontal = seed(i * 3) > 0.5;
      items.push({
        x: 200 + seed(i * 7) * (CANVAS_WIDTH - 400),
        y: 100 + seed(i * 11) * (CANVAS_HEIGHT - 200),
        size: 2,
        type: 'line',
        angle: isHorizontal ? 0 : Math.PI / 2,
        velocityX: (seed(i * 13) - 0.5) * 8,
        velocityY: (seed(i * 17) - 0.5) * 8,
        rotationSpeed: (seed(i * 19) - 0.5) * 0.15,
        width: 40 + seed(i * 23) * 100,
        height: 2,
      });
    }

    // Junction nodes (small squares / circles)
    for (let i = 0; i < 40; i++) {
      items.push({
        x: 250 + seed(i * 31 + 100) * (CANVAS_WIDTH - 500),
        y: 120 + seed(i * 37 + 100) * (CANVAS_HEIGHT - 240),
        size: 4 + seed(i * 41 + 100) * 6,
        type: 'node',
        angle: 0,
        velocityX: (seed(i * 43 + 100) - 0.5) * 10,
        velocityY: (seed(i * 47 + 100) - 0.5) * 10,
        rotationSpeed: (seed(i * 53 + 100) - 0.5) * 0.2,
        width: 0,
        height: 0,
      });
    }

    // Diagonal connections
    for (let i = 0; i < 25; i++) {
      items.push({
        x: 300 + seed(i * 59 + 200) * (CANVAS_WIDTH - 600),
        y: 150 + seed(i * 61 + 200) * (CANVAS_HEIGHT - 300),
        size: 2,
        type: 'line',
        angle: seed(i * 67 + 200) * Math.PI,
        velocityX: (seed(i * 71 + 200) - 0.5) * 12,
        velocityY: (seed(i * 73 + 200) - 0.5) * 12,
        rotationSpeed: (seed(i * 79 + 200) - 0.5) * 0.1,
        width: 30 + seed(i * 83 + 200) * 60,
        height: 2,
      });
    }

    return items;
  }, []);

  // Dissolve progress: 0 = intact, 1 = fully dissolved
  const dissolveProgress = interpolate(
    frame,
    [DISSOLVE_START, DISSOLVE_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.quad) }
  );

  // Overall opacity fades out
  const overallOpacity = interpolate(
    frame,
    [DISSOLVE_START, DISSOLVE_END * 0.7, DISSOLVE_END],
    [0.85, 0.5, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  if (frame >= DISSOLVE_END) return null;

  return (
    <AbsoluteFill style={{ opacity: overallOpacity }}>
      <svg width={CANVAS_WIDTH} height={CANVAS_HEIGHT}>
        {particles.map((p, i) => {
          const dx = p.velocityX * dissolveProgress * 8;
          const dy = p.velocityY * dissolveProgress * 8;
          const rotation = p.angle + p.rotationSpeed * dissolveProgress * 60;
          const px = p.x + dx;
          const py = p.y + dy;

          if (p.type === 'line') {
            return (
              <g
                key={`line-${i}`}
                transform={`translate(${px}, ${py}) rotate(${(rotation * 180) / Math.PI})`}
              >
                <rect
                  x={-p.width / 2}
                  y={-1}
                  width={p.width}
                  height={p.height}
                  fill={SCHEMATIC_LINE_COLOR}
                  rx={1}
                />
              </g>
            );
          }

          return (
            <g
              key={`node-${i}`}
              transform={`translate(${px}, ${py}) rotate(${(rotation * 180) / Math.PI})`}
            >
              <rect
                x={-p.size / 2}
                y={-p.size / 2}
                width={p.size}
                height={p.size}
                fill={SCHEMATIC_NODE_COLOR}
                rx={1}
              />
            </g>
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};
