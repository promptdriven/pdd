import React from 'react';

type IconType = 'film' | 'clock' | 'sparkle';

interface MetricIconProps {
  icon: IconType;
  color: string;
  size: number;
  rotation?: number;
}

export const MetricIcon: React.FC<MetricIconProps> = ({
  icon,
  color,
  size,
  rotation = 0,
}) => {
  const style: React.CSSProperties = {
    width: size,
    height: size,
    transform: `rotate(${rotation}deg)`,
  };

  if (icon === 'film') {
    return (
      <svg
        style={style}
        viewBox="0 0 24 24"
        fill="none"
        stroke={color}
        strokeWidth={2}
        strokeLinecap="round"
        strokeLinejoin="round"
      >
        <rect x="2" y="2" width="20" height="20" rx="2" />
        <line x1="7" y1="2" x2="7" y2="22" />
        <line x1="17" y1="2" x2="17" y2="22" />
        <line x1="2" y1="7" x2="7" y2="7" />
        <line x1="2" y1="12" x2="22" y2="12" />
        <line x1="2" y1="17" x2="7" y2="17" />
        <line x1="17" y1="7" x2="22" y2="7" />
        <line x1="17" y1="17" x2="22" y2="17" />
      </svg>
    );
  }

  if (icon === 'clock') {
    return (
      <svg
        style={style}
        viewBox="0 0 24 24"
        fill="none"
        stroke={color}
        strokeWidth={2}
        strokeLinecap="round"
        strokeLinejoin="round"
      >
        <circle cx="12" cy="12" r="10" />
        <polyline points="12 6 12 12 16 14" />
      </svg>
    );
  }

  // sparkle
  return (
    <svg
      style={style}
      viewBox="0 0 24 24"
      fill="none"
      stroke={color}
      strokeWidth={2}
      strokeLinecap="round"
      strokeLinejoin="round"
    >
      <path d="M12 2L13.5 8.5L20 7L15 12L20 17L13.5 15.5L12 22L10.5 15.5L4 17L9 12L4 7L10.5 8.5L12 2Z" />
    </svg>
  );
};
