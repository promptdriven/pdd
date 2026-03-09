import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface FlowNodeProps {
  label: string;
  borderColor: string;
  filled: boolean;
  icon: 'cursor' | 'sparkle' | 'film';
  animStartFrame: number;
  animEndFrame: number;
  showGlow: boolean;
}

const CursorIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width="24" height="24" viewBox="0 0 24 24" fill="none">
    <path
      d="M5 3L19 12L12 13L9 20L5 3Z"
      stroke={color}
      strokeWidth={2}
      strokeLinejoin="round"
    />
  </svg>
);

const SparkleIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width="24" height="24" viewBox="0 0 24 24" fill="none">
    <path
      d="M12 2L13.5 8.5L20 10L13.5 11.5L12 18L10.5 11.5L4 10L10.5 8.5L12 2Z"
      fill={color}
      stroke={color}
      strokeWidth={1}
      strokeLinejoin="round"
    />
  </svg>
);

const FilmIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width="24" height="24" viewBox="0 0 24 24" fill="none">
    <rect x="3" y="5" width="18" height="14" rx="2" stroke={color} strokeWidth={2} />
    <line x1="3" y1="9" x2="21" y2="9" stroke={color} strokeWidth={1.5} />
    <line x1="3" y1="15" x2="21" y2="15" stroke={color} strokeWidth={1.5} />
    <line x1="7" y1="5" x2="7" y2="9" stroke={color} strokeWidth={1.5} />
    <line x1="17" y1="5" x2="17" y2="9" stroke={color} strokeWidth={1.5} />
    <line x1="7" y1="15" x2="7" y2="19" stroke={color} strokeWidth={1.5} />
    <line x1="17" y1="15" x2="17" y2="19" stroke={color} strokeWidth={1.5} />
  </svg>
);

const IconMap: Record<string, React.FC<{ color: string }>> = {
  cursor: CursorIcon,
  sparkle: SparkleIcon,
  film: FilmIcon,
};

export const FlowNode: React.FC<FlowNodeProps> = ({
  label,
  borderColor,
  filled,
  icon,
  animStartFrame,
  animEndFrame,
  showGlow,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [animStartFrame, animEndFrame],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // easeOutBack: slight overshoot for scale
  const rawScale = interpolate(
    frame,
    [animStartFrame, animEndFrame],
    [0.8, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    },
  );
  const scale = rawScale;

  // Amber glow pulse for Veo AI node
  const glowOpacity = showGlow
    ? interpolate(
        frame % 30,
        [0, 15, 30],
        [0.3, 0.8, 0.3],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
      )
    : 0;

  const IconComponent = IconMap[icon];

  return (
    <div
      style={{
        width: 160,
        height: 80,
        borderRadius: 12,
        border: `2px solid ${borderColor}`,
        backgroundColor: filled ? 'rgba(245, 158, 11, 0.15)' : 'transparent',
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'center',
        gap: 6,
        opacity,
        transform: `scale(${scale})`,
        position: 'relative',
        flexShrink: 0,
      }}
    >
      {/* Glow effect behind node */}
      {showGlow && (
        <div
          style={{
            position: 'absolute',
            inset: -8,
            borderRadius: 20,
            background: `radial-gradient(circle, ${borderColor}40 0%, transparent 70%)`,
            opacity: glowOpacity,
            pointerEvents: 'none',
          }}
        />
      )}
      {IconComponent && <IconComponent color={borderColor} />}
      <span
        style={{
          color: '#FFFFFF',
          fontSize: 16,
          fontFamily: 'Inter, sans-serif',
          fontWeight: 600,
        }}
      >
        {label}
      </span>
    </div>
  );
};
