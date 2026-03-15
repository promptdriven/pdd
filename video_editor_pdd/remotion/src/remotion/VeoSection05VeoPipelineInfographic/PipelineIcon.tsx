import React from 'react';

type IconType = 'text' | 'sparkle' | 'film';

interface PipelineIconProps {
  type: IconType;
  color: string;
  size: number;
}

const TextIcon: React.FC<{ color: string; size: number }> = ({
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
    <path d="M4 7V4h16v3" />
    <line x1="12" y1="4" x2="12" y2="20" />
    <line x1="8" y1="20" x2="16" y2="20" />
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
    <path d="M12 2l2.4 7.2L22 12l-7.6 2.8L12 22l-2.4-7.2L2 12l7.6-2.8z" />
    <circle cx="19" cy="5" r="1.5" />
    <circle cx="5" cy="19" r="1" />
  </svg>
);

const FilmIcon: React.FC<{ color: string; size: number }> = ({
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
    <rect x="2" y="2" width="20" height="20" rx="2" />
    <line x1="2" y1="7" x2="22" y2="7" />
    <line x1="2" y1="17" x2="22" y2="17" />
    <line x1="7" y1="2" x2="7" y2="7" />
    <line x1="17" y1="2" x2="17" y2="7" />
    <line x1="7" y1="17" x2="7" y2="22" />
    <line x1="17" y1="17" x2="17" y2="22" />
  </svg>
);

export const PipelineIcon: React.FC<PipelineIconProps> = ({
  type,
  color,
  size,
}) => {
  switch (type) {
    case 'text':
      return <TextIcon color={color} size={size} />;
    case 'sparkle':
      return <SparkleIcon color={color} size={size} />;
    case 'film':
      return <FilmIcon color={color} size={size} />;
    default:
      return null;
  }
};
