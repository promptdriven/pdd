import React from 'react';
import { COLORS, DIMENSIONS } from './constants';

export const CodeBracketIcon: React.FC = () => {
  const size = DIMENSIONS.iconSize;
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 40 40"
      fill="none"
      xmlns="http://www.w3.org/2000/svg"
    >
      {/* Left bracket < */}
      <path
        d="M15 8L5 20L15 32"
        stroke={COLORS.codeIcon}
        strokeWidth="3"
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
      {/* Right bracket > */}
      <path
        d="M25 8L35 20L25 32"
        stroke={COLORS.codeIcon}
        strokeWidth="3"
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
      {/* Slash / */}
      <path
        d="M22 6L18 34"
        stroke={COLORS.codeIcon}
        strokeWidth="2"
        strokeLinecap="round"
        fill="none"
      />
    </svg>
  );
};
