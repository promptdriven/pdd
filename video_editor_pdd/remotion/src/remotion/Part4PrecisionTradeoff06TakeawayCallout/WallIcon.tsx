import React from 'react';
import { AMBER } from './constants';

interface WallIconProps {
  size?: number;
  color?: string;
  opacity?: number;
}

export const WallIcon: React.FC<WallIconProps> = ({
  size = 8,
  color = AMBER,
  opacity = 1,
}) => {
  const w = size;
  const h = size * 1.4;
  return (
    <svg
      width={w}
      height={h}
      viewBox="0 0 10 14"
      style={{ display: 'inline-block', verticalAlign: 'middle', opacity, marginRight: 4 }}
    >
      {/* Brick wall pattern */}
      <rect x="0" y="0" width="10" height="3" rx="0.5" fill={color} />
      <rect x="0" y="4" width="4.5" height="3" rx="0.5" fill={color} />
      <rect x="5.5" y="4" width="4.5" height="3" rx="0.5" fill={color} />
      <rect x="0" y="8" width="10" height="3" rx="0.5" fill={color} />
      <rect x="0" y="12" width="4.5" height="2" rx="0.5" fill={color} />
      <rect x="5.5" y="12" width="4.5" height="2" rx="0.5" fill={color} />
    </svg>
  );
};

export default WallIcon;
