import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface MoldCrossSectionProps {
  x: number;
  y: number;
  width: number;
  height: number;
  wallCount: number;
  wallColor: string;
  wallOpacity: number;
  wallStroke: number;
  fillColor: string;
  fillOpacity: number;
  animationStart: number;
  glow?: { color: string; blur: number; opacity: number };
}

export const MoldCrossSection: React.FC<MoldCrossSectionProps> = ({
  x,
  y,
  width,
  height,
  wallCount,
  wallColor,
  wallOpacity,
  wallStroke,
  fillColor,
  fillOpacity,
  animationStart,
  glow,
}) => {
  const frame = useCurrentFrame();

  // Overall section fade in
  const sectionOpacity = interpolate(
    frame,
    [animationStart, animationStart + 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Generate wall segments as SVG lines within the mold
  const generateWalls = () => {
    const walls: Array<{ x1: number; y1: number; x2: number; y2: number }> = [];
    const margin = 8;
    const innerW = width - margin * 2;
    const innerH = height - margin * 2;

    // Outer border walls (always present)
    // top
    walls.push({ x1: margin, y1: margin, x2: width - margin, y2: margin });
    // bottom
    walls.push({ x1: margin, y1: height - margin, x2: width - margin, y2: height - margin });
    // left
    walls.push({ x1: margin, y1: margin, x2: margin, y2: height - margin });

    // Generate internal walls (horizontal and vertical partitions)
    const internalCount = Math.max(0, wallCount - 3);
    for (let i = 0; i < internalCount; i++) {
      const isHorizontal = i % 2 === 0;
      if (isHorizontal) {
        // Horizontal internal wall
        const yPos = margin + (innerH * ((i / 2 + 1) / (Math.ceil(internalCount / 2) + 1)));
        const xStart = margin + (i % 4 === 0 ? 0 : innerW * 0.2);
        const xEnd = margin + (i % 4 === 2 ? innerW : innerW * 0.8);
        walls.push({ x1: xStart, y1: yPos, x2: xEnd, y2: yPos });
      } else {
        // Vertical internal wall
        const xPos = margin + (innerW * ((Math.floor(i / 2) + 1) / (Math.ceil(internalCount / 2) + 1)));
        const yStart = margin + (i % 4 === 1 ? 0 : innerH * 0.15);
        const yEnd = margin + (i % 4 === 3 ? innerH : innerH * 0.85);
        walls.push({ x1: xPos, y1: yStart, x2: xPos, y2: yEnd });
      }
    }

    return walls;
  };

  const walls = generateWalls();

  // Glow animation for Stage 3
  const glowOpacity = glow
    ? interpolate(
        frame,
        [animationStart + 25, animationStart + 35, animationStart + 45],
        [0, glow.opacity, glow.opacity * 0.5],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
        opacity: sectionOpacity,
      }}
    >
      <svg width={width} height={height} viewBox={`0 0 ${width} ${height}`}>
        {/* Interior fill */}
        <rect
          x={8}
          y={8}
          width={width - 16}
          height={height - 16}
          fill={fillColor}
          opacity={fillOpacity}
          rx={2}
        />
        {/* Wall segments with staggered draw-in */}
        {walls.map((wall, i) => {
          const wallStart = animationStart + 5 + i * (20 / Math.max(walls.length, 1));
          const drawProgress = interpolate(
            frame,
            [wallStart, wallStart + 10],
            [0, 1],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.inOut(Easing.cubic),
            }
          );

          const dx = wall.x2 - wall.x1;
          const dy = wall.y2 - wall.y1;

          return (
            <line
              key={i}
              x1={wall.x1}
              y1={wall.y1}
              x2={wall.x1 + dx * drawProgress}
              y2={wall.y1 + dy * drawProgress}
              stroke={wallColor}
              strokeOpacity={wallOpacity}
              strokeWidth={wallStroke}
              strokeLinecap="round"
            />
          );
        })}
      </svg>
      {/* Glow effect for Stage 3 */}
      {glow && (
        <div
          style={{
            position: 'absolute',
            inset: 0,
            borderRadius: 4,
            boxShadow: `0 0 ${glow.blur}px ${glow.color}, inset 0 0 ${glow.blur / 2}px ${glow.color}`,
            opacity: glowOpacity,
            pointerEvents: 'none',
          }}
        />
      )}
    </div>
  );
};
