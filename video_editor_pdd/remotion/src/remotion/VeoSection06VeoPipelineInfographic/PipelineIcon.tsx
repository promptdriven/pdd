import React from 'react';

type IconType = 'document' | 'sparkle' | 'film' | 'layers';

interface PipelineIconProps {
  type: IconType;
  color: string;
  size: number;
}

const DocumentIcon: React.FC<{ color: string; size: number }> = ({
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
    <path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z" />
    <polyline points="14 2 14 8 20 8" />
    <line x1="16" y1="13" x2="8" y2="13" />
    <line x1="16" y1="17" x2="8" y2="17" />
    <line x1="10" y1="9" x2="8" y2="9" />
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
    <rect x="2" y="2" width="20" height="20" rx="2.18" ry="2.18" />
    <line x1="7" y1="2" x2="7" y2="22" />
    <line x1="17" y1="2" x2="17" y2="22" />
    <line x1="2" y1="12" x2="22" y2="12" />
    <line x1="2" y1="7" x2="7" y2="7" />
    <line x1="2" y1="17" x2="7" y2="17" />
    <line x1="17" y1="7" x2="22" y2="7" />
    <line x1="17" y1="17" x2="22" y2="17" />
  </svg>
);

const LayersIcon: React.FC<{ color: string; size: number }> = ({
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
    <polygon points="12 2 2 7 12 12 22 7 12 2" />
    <polyline points="2 17 12 22 22 17" />
    <polyline points="2 12 12 17 22 12" />
  </svg>
);

export const PipelineIcon: React.FC<PipelineIconProps> = ({
  type,
  color,
  size,
}) => {
  switch (type) {
    case 'document':
      return <DocumentIcon color={color} size={size} />;
    case 'sparkle':
      return <SparkleIcon color={color} size={size} />;
    case 'film':
      return <FilmIcon color={color} size={size} />;
    case 'layers':
      return <LayersIcon color={color} size={size} />;
    default:
      return null;
  }
};
