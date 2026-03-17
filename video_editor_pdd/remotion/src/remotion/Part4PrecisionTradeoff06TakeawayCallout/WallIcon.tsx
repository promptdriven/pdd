import React from 'react';

interface WallIconProps {
  size: number;
  color: string;
  opacity?: number;
}

/**
 * A small inline wall icon — three vertical brick-like bars
 * reminiscent of a mold wall / constraint boundary.
 */
export const WallIcon: React.FC<WallIconProps> = ({
  size,
  color,
  opacity = 1,
}) => {
  const w = size;
  const h = size * 1.4;
  const barW = w * 0.22;
  const gap = (w - barW * 3) / 2;

  return (
    <svg
      width={w}
      height={h}
      viewBox={`0 0 ${w} ${h}`}
      style={{ display: 'inline-block', verticalAlign: 'middle', opacity }}
    >
      {[0, 1, 2].map((i) => (
        <rect
          key={i}
          x={i * (barW + gap)}
          y={0}
          width={barW}
          height={h}
          rx={barW * 0.2}
          fill={color}
        />
      ))}
    </svg>
  );
};

export default WallIcon;
