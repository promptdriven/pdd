import React from 'react';
import { COLORS, DIMENSIONS } from './constants';

export const FilmReelIcon: React.FC = () => {
  const size = DIMENSIONS.filmReelSize;
  const color = COLORS.filmReelIcon;

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: '50%',
        transform: 'translate(-50%, -50%)',
        width: size,
        height: size,
        opacity: 0.3,
      }}
    >
      <svg
        width={size}
        height={size}
        viewBox="0 0 120 120"
        fill="none"
        xmlns="http://www.w3.org/2000/svg"
      >
        {/* Outer circle (film reel) */}
        <circle cx="60" cy="60" r="54" stroke={color} strokeWidth="4" />
        {/* Inner circle */}
        <circle cx="60" cy="60" r="20" stroke={color} strokeWidth="3" />
        {/* Center dot */}
        <circle cx="60" cy="60" r="6" fill={color} />
        {/* Sprocket holes around the reel */}
        {[0, 45, 90, 135, 180, 225, 270, 315].map((angle) => {
          const rad = (angle * Math.PI) / 180;
          const cx = 60 + 38 * Math.cos(rad);
          const cy = 60 + 38 * Math.sin(rad);
          return (
            <circle key={angle} cx={cx} cy={cy} r="6" fill={color} opacity={0.6} />
          );
        })}
        {/* Film strip perforations on left/right */}
        {[20, 40, 60, 80, 100].map((y) => (
          <React.Fragment key={y}>
            <rect x="2" y={y - 4} width="8" height="8" rx="1" fill={color} opacity={0.4} />
            <rect x="110" y={y - 4} width="8" height="8" rx="1" fill={color} opacity={0.4} />
          </React.Fragment>
        ))}
      </svg>
    </div>
  );
};
