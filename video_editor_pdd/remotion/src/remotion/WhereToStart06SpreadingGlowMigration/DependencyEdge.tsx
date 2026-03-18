import React from 'react';
import { EDGE_UNCONVERTED, EDGE_CONVERTED, BLUE_ACCENT } from './constants';

interface DependencyEdgeProps {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
  /** 0 = fully unconverted style, 1 = fully converted (both endpoints converted) */
  brightenProgress: number;
}

const DependencyEdge: React.FC<DependencyEdgeProps> = ({
  x1,
  y1,
  x2,
  y2,
  brightenProgress,
}) => {
  const t = brightenProgress;
  const opacity =
    EDGE_UNCONVERTED.opacity + (EDGE_CONVERTED.opacity - EDGE_UNCONVERTED.opacity) * t;
  const width =
    EDGE_UNCONVERTED.width + (EDGE_CONVERTED.width - EDGE_UNCONVERTED.width) * t;

  // Interpolate color from gray to blue
  const color = t > 0.01 ? BLUE_ACCENT : EDGE_UNCONVERTED.color;

  return (
    <line
      x1={x1}
      y1={y1}
      x2={x2}
      y2={y2}
      stroke={color}
      strokeOpacity={opacity}
      strokeWidth={width}
    />
  );
};

export default DependencyEdge;
