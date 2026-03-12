import React from 'react';

type IconType = 'text-cursor' | 'sparkle' | 'play-circle';

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
    <line x1="7" y1="12" x2="17" y2="12" />
  </svg>
);

const SparkleIcon: React.FC<{ color: string; size: number }> = ({
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
    <path d="M12 2l2.4 7.2L22 12l-7.6 2.8L12 22l-2.4-7.2L2 12l7.6-2.8L12 2z" />
  </svg>
);

const PlayCircleIcon: React.FC<{ color: string; size: number }> = ({
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
    <circle cx="12" cy="12" r="10" />
    <polygon points="10,8 16,12 10,16" fill={color} stroke="none" />
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
    case 'sparkle':
      return <SparkleIcon color={color} size={size} />;
    case 'play-circle':
      return <PlayCircleIcon color={color} size={size} />;
    default:
      return null;
  }
};
