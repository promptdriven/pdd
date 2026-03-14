import React from 'react';

type IconType = 'text-cursor' | 'brain' | 'play';

interface PipelineIconProps {
  type: IconType;
  color: string;
  size: number;
}

const TextCursorIcon: React.FC<{ color: string; size: number }> = ({
  color,
  size,
}) => (
  <svg
    width={size}
    height={size}
    viewBox="0 0 24 24"
    fill="none"
    stroke={color}
    strokeWidth={2}
    strokeLinecap="round"
    strokeLinejoin="round"
  >
    <path d="M17 22h-1a4 4 0 0 1-4-4V6a4 4 0 0 1 4-4h1" />
    <path d="M7 22h1a4 4 0 0 0 4-4V6a4 4 0 0 0-4-4H7" />
    <line x1="9" y1="12" x2="15" y2="12" />
  </svg>
);

const BrainIcon: React.FC<{ color: string; size: number }> = ({
  color,
  size,
}) => (
  <svg
    width={size}
    height={size}
    viewBox="0 0 24 24"
    fill="none"
    stroke={color}
    strokeWidth={2}
    strokeLinecap="round"
    strokeLinejoin="round"
  >
    <path d="M12 2a4 4 0 0 1 4 4c1.7 0 3 1.3 3 3 1.1 0 2 .9 2 2s-.9 2-2 2c0 1.7-1.3 3-3 3a4 4 0 0 1-4 4" />
    <path d="M12 2a4 4 0 0 0-4 4c-1.7 0-3 1.3-3 3-1.1 0-2 .9-2 2s.9 2 2 2c0 1.7 1.3 3 3 3a4 4 0 0 0 4 4" />
    <line x1="12" y1="2" x2="12" y2="22" />
    <path d="M8 8h0" />
    <path d="M16 8h0" />
    <path d="M8 16h0" />
    <path d="M16 16h0" />
  </svg>
);

const PlayIcon: React.FC<{ color: string; size: number }> = ({
  color,
  size,
}) => (
  <svg
    width={size}
    height={size}
    viewBox="0 0 24 24"
    fill={color}
    stroke="none"
  >
    <polygon points="5,3 19,12 5,21" />
  </svg>
);

export const PipelineIcon: React.FC<PipelineIconProps> = ({
  type,
  color,
  size,
}) => {
  switch (type) {
    case 'text-cursor':
      return <TextCursorIcon color={color} size={size} />;
    case 'brain':
      return <BrainIcon color={color} size={size} />;
    case 'play':
      return <PlayIcon color={color} size={size} />;
    default:
      return null;
  }
};
