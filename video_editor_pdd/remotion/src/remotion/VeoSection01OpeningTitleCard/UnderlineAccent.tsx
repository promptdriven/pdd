/**
 * UnderlineAccent Component
 *
 * Animated underline that draws from center outward
 */

import React from 'react';
import { COLORS, DIMENSIONS } from './constants';

interface UnderlineAccentProps {
  width: number;
}

export const UnderlineAccent: React.FC<UnderlineAccentProps> = ({ width }) => {
  return (
    <div
      style={{
        position: 'absolute',
        top: '50%',
        left: '50%',
        transform: 'translate(-50%, -50%)',
        marginTop: 80, // Position below title
        width,
        height: DIMENSIONS.underline.height,
        backgroundColor: COLORS.accent,
        borderRadius: 2,
      }}
    />
  );
};
