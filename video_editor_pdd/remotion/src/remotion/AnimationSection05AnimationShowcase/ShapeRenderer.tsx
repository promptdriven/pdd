import React from 'react';
import type { ShapeType } from './constants';
import { SHADOW } from './constants';

interface ShapeRendererProps {
  type: ShapeType;
  color: string;
  size: number;
  style?: React.CSSProperties;
}

export const ShapeRenderer: React.FC<ShapeRendererProps> = ({
  type,
  color,
  size,
  style,
}) => {
  if (type === 'circle') {
    return (
      <div
        style={{
          width: size,
          height: size,
          borderRadius: '50%',
          backgroundColor: color,
          boxShadow: SHADOW,
          ...style,
        }}
      />
    );
  }

  if (type === 'square') {
    return (
      <div
        style={{
          width: size,
          height: size,
          borderRadius: 6,
          backgroundColor: color,
          boxShadow: SHADOW,
          ...style,
        }}
      />
    );
  }

  // Triangle via CSS borders
  const halfBase = size / 2;
  const triangleHeight = size * 0.866; // equilateral triangle height
  return (
    <div
      style={{
        width: 0,
        height: 0,
        borderLeft: `${halfBase}px solid transparent`,
        borderRight: `${halfBase}px solid transparent`,
        borderBottom: `${triangleHeight}px solid ${color}`,
        filter: 'drop-shadow(0 8px 24px rgba(0, 0, 0, 0.3))',
        ...style,
      }}
    />
  );
};
