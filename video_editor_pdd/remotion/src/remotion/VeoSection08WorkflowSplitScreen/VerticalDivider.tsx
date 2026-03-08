/**
 * VerticalDivider - Gradient divider between workflows
 */

import React from 'react';
import { COLORS, DIMENSIONS } from './constants';

interface VerticalDividerProps {
  x?: number;
  height?: number;
}

export const VerticalDivider: React.FC<VerticalDividerProps> = ({
  x = DIMENSIONS.divider.x,
  height = DIMENSIONS.canvas.height,
}) => {
  return (
    <div
      style={{
        position: 'absolute',
        left: x - DIMENSIONS.divider.width / 2,
        top: 0,
        width: DIMENSIONS.divider.width,
        height,
        background: `linear-gradient(to bottom, ${COLORS.traditional.primary}, ${COLORS.veo2.primary})`,
      }}
    />
  );
};
