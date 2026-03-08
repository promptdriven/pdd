/**
 * TitleCard Component
 *
 * Main title text with animated scale and opacity
 */

import React from 'react';
import { COLORS, DIMENSIONS } from './constants';

interface TitleCardProps {
  text: string;
  scale: number;
  opacity: number;
}

export const TitleCard: React.FC<TitleCardProps> = ({ text, scale, opacity }) => {
  return (
    <div
      style={{
        position: 'absolute',
        top: '50%',
        left: '50%',
        transform: `translate(-50%, -50%) scale(${scale})`,
        opacity,
        fontFamily: 'Inter, sans-serif',
        fontWeight: 900,
        fontSize: DIMENSIONS.title.fontSize,
        letterSpacing: DIMENSIONS.title.letterSpacing,
        color: COLORS.title,
        textAlign: 'center',
        whiteSpace: 'nowrap',
      }}
    >
      {text}
    </div>
  );
};
