import React from 'react';
import { COLORS, DIMENSIONS } from './constants';

export const FilmReelIcon: React.FC = () => {
  const size = DIMENSIONS.iconSize;
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 40 40"
      fill="none"
      xmlns="http://www.w3.org/2000/svg"
    >
      {/* Film reel outer circle */}
      <circle cx="20" cy="20" r="18" stroke={COLORS.filmIcon} strokeWidth="2" fill="none" />
      {/* Center hole */}
      <circle cx="20" cy="20" r="4" fill={COLORS.filmIcon} />
      {/* Sprocket holes */}
      <circle cx="20" cy="6" r="2.5" fill={COLORS.filmIcon} />
      <circle cx="20" cy="34" r="2.5" fill={COLORS.filmIcon} />
      <circle cx="6" cy="20" r="2.5" fill={COLORS.filmIcon} />
      <circle cx="34" cy="20" r="2.5" fill={COLORS.filmIcon} />
      {/* Diagonal sprockets */}
      <circle cx="10" cy="10" r="2" fill={COLORS.filmIcon} />
      <circle cx="30" cy="10" r="2" fill={COLORS.filmIcon} />
      <circle cx="10" cy="30" r="2" fill={COLORS.filmIcon} />
      <circle cx="30" cy="30" r="2" fill={COLORS.filmIcon} />
    </svg>
  );
};
