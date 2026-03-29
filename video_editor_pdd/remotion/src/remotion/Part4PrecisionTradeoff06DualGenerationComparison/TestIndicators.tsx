import React, { useMemo } from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface TestIndicatorsProps {
  count: number;
  dotSize: number;
  color: string;
  dotOpacity: number;
  targetX: number;
  targetY: number;
  targetW: number;
  targetH: number;
  appearStart: number;
  appearDuration: number;
}

const TestIndicators: React.FC<TestIndicatorsProps> = ({
  count,
  dotSize,
  color,
  dotOpacity,
  targetX,
  targetY,
  targetW,
  targetH,
  appearStart,
  appearDuration,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [appearStart, appearStart + appearDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Arrange dots around the prompt file in a frame pattern
  const dots = useMemo(() => {
    const positions: { x: number; y: number }[] = [];
    const spacing = 10;
    const margin = 14;

    // Top edge
    let placed = 0;
    const topY = targetY - margin;
    for (let dx = 0; placed < count; dx += spacing) {
      if (dx > targetW + margin * 2) break;
      positions.push({ x: targetX - margin + dx, y: topY });
      placed++;
    }

    // Right edge
    const rightX = targetX + targetW + margin;
    for (let dy = 0; placed < count; dy += spacing) {
      if (dy > targetH + margin * 2) break;
      positions.push({ x: rightX, y: targetY - margin + dy });
      placed++;
    }

    // Bottom edge (right to left)
    const bottomY = targetY + targetH + margin;
    for (let dx = targetW + margin * 2; placed < count; dx -= spacing) {
      if (dx < 0) break;
      positions.push({ x: targetX - margin + dx, y: bottomY });
      placed++;
    }

    // Left edge (bottom to top)
    const leftX = targetX - margin;
    for (let dy = targetH + margin * 2; placed < count; dy -= spacing) {
      if (dy < 0) break;
      positions.push({ x: leftX, y: targetY - margin + dy });
      placed++;
    }

    return positions.slice(0, count);
  }, [count, targetX, targetY, targetW, targetH]);

  return (
    <div style={{ position: 'absolute', left: 0, top: 0, opacity }}>
      {dots.map((pos, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            left: pos.x,
            top: pos.y,
            width: dotSize,
            height: dotSize,
            backgroundColor: color,
            opacity: dotOpacity,
            borderRadius: 1,
          }}
        />
      ))}
    </div>
  );
};

export default TestIndicators;
