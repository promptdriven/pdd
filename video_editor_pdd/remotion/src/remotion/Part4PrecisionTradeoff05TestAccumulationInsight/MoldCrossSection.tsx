import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface GlowConfig {
  color: string;
  blur: number;
  opacity: number;
}

interface MoldCrossSectionProps {
  width: number;
  height: number;
  wallCount: number;
  wallColor: string;
  wallStroke: number;
  fillColor: string;
  fillOpacity: number;
  animStartFrame: number;
  animDuration: number;
  glow?: GlowConfig;
}

/**
 * Renders a mold cross-section with wall segments and interior fill.
 * Walls draw in with easeInOut animation.
 */
const MoldCrossSection: React.FC<MoldCrossSectionProps> = ({
  width,
  height,
  wallCount,
  wallColor,
  wallStroke,
  fillColor,
  fillOpacity,
  animStartFrame,
  animDuration,
  glow,
}) => {
  const frame = useCurrentFrame();
  const svgWidth = width;
  const svgHeight = height;
  const inset = 8;

  // Overall draw progress for all walls
  const wallsProgress = interpolate(
    frame,
    [animStartFrame, animStartFrame + animDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // Generate wall segments distributed within the mold
  const walls: Array<{ x1: number; y1: number; x2: number; y2: number }> = [];

  if (wallCount <= 6) {
    // Few walls: simple horizontal + vertical partitions
    const hCount = Math.ceil(wallCount / 2);
    const vCount = wallCount - hCount;
    for (let i = 0; i < hCount; i++) {
      const y = inset + ((svgHeight - inset * 2) / (hCount + 1)) * (i + 1);
      walls.push({
        x1: inset + 5,
        y1: y,
        x2: svgWidth - inset - 5,
        y2: y,
      });
    }
    for (let i = 0; i < vCount; i++) {
      const x = inset + ((svgWidth - inset * 2) / (vCount + 1)) * (i + 1);
      walls.push({
        x1: x,
        y1: inset + 5,
        x2: x,
        y2: svgHeight - inset - 5,
      });
    }
  } else {
    // Many walls: grid-like pattern with some diagonal variation
    const gridCols = Math.ceil(Math.sqrt(wallCount * (svgWidth / svgHeight)));
    const gridRows = Math.ceil(wallCount / gridCols);
    const cellW = (svgWidth - inset * 2) / gridCols;
    const cellH = (svgHeight - inset * 2) / gridRows;

    let wallIdx = 0;
    for (let r = 0; r < gridRows && wallIdx < wallCount; r++) {
      for (let c = 0; c < gridCols && wallIdx < wallCount; c++) {
        const cx = inset + c * cellW + cellW / 2;
        const cy = inset + r * cellH + cellH / 2;
        const halfLen = Math.min(cellW, cellH) * 0.4;

        // Alternate between horizontal, vertical, and diagonal walls
        const variant = wallIdx % 3;
        if (variant === 0) {
          // Horizontal
          walls.push({ x1: cx - halfLen, y1: cy, x2: cx + halfLen, y2: cy });
        } else if (variant === 1) {
          // Vertical
          walls.push({ x1: cx, y1: cy - halfLen, x2: cx, y2: cy + halfLen });
        } else {
          // Diagonal
          walls.push({
            x1: cx - halfLen * 0.7,
            y1: cy - halfLen * 0.7,
            x2: cx + halfLen * 0.7,
            y2: cy + halfLen * 0.7,
          });
        }
        wallIdx++;
      }
    }
  }

  // Glow animation for Stage 3
  const glowOpacity = glow
    ? interpolate(
        frame,
        [animStartFrame + animDuration, animStartFrame + animDuration + 20, animStartFrame + animDuration + 40],
        [0, glow.opacity, 0],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : 0;

  return (
    <div style={{ width, height, position: 'relative' }}>
      <svg
        width={svgWidth}
        height={svgHeight}
        viewBox={`0 0 ${svgWidth} ${svgHeight}`}
        style={{ display: 'block' }}
      >
        {/* Interior fill */}
        <rect
          x={inset}
          y={inset}
          width={svgWidth - inset * 2}
          height={svgHeight - inset * 2}
          fill={fillColor}
          opacity={fillOpacity * wallsProgress}
          rx={2}
        />

        {/* Outer border (the mold frame) */}
        <rect
          x={inset}
          y={inset}
          width={svgWidth - inset * 2}
          height={svgHeight - inset * 2}
          fill="none"
          stroke={wallColor}
          strokeWidth={wallStroke}
          opacity={0.7 * Math.min(1, wallsProgress * 3)}
          rx={2}
        />

        {/* Wall segments */}
        {walls.map((wall, i) => {
          const wallFraction = (i + 1) / walls.length;
          const wallVisible = wallsProgress >= wallFraction ? 1 : wallsProgress >= wallFraction - 1 / walls.length
            ? interpolate(
                wallsProgress,
                [wallFraction - 1 / walls.length, wallFraction],
                [0, 1],
                { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
              )
            : 0;

          const dx = wall.x2 - wall.x1;
          const dy = wall.y2 - wall.y1;
          const len = Math.sqrt(dx * dx + dy * dy);
          const dashOffset = len * (1 - wallVisible);

          return (
            <line
              key={i}
              x1={wall.x1}
              y1={wall.y1}
              x2={wall.x2}
              y2={wall.y2}
              stroke={wallColor}
              strokeWidth={wallStroke}
              opacity={0.7}
              strokeDasharray={len}
              strokeDashoffset={dashOffset}
              strokeLinecap="round"
            />
          );
        })}
      </svg>

      {/* Glow overlay */}
      {glow && glowOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: -glow.blur,
            width: width + glow.blur * 2,
            height: height + glow.blur * 2,
            borderRadius: 6,
            boxShadow: `0 0 ${glow.blur}px ${glow.blur / 2}px ${glow.color}`,
            opacity: glowOpacity,
            pointerEvents: 'none',
          }}
        />
      )}
    </div>
  );
};

export default MoldCrossSection;
