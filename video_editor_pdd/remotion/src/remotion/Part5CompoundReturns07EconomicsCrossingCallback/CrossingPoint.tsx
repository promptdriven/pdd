// CrossingPoint.tsx — Pulsing crossing point with glow and label
import React from 'react';
import { useCurrentFrame } from 'remotion';
import { COLORS, OPACITIES } from './constants';

interface CrossingPointProps {
  /** Pixel X position of the crossing point */
  cx: number;
  /** Pixel Y position of the crossing point */
  cy: number;
  /** Label to show above the crossing point */
  label: string;
  /** Whether the pulse is active */
  pulsing: boolean;
  /** Overall opacity */
  opacity: number;
}

/**
 * Renders the crossing point circle with a pulsing glow effect
 * and a label above it.
 */
export const CrossingPoint: React.FC<CrossingPointProps> = ({
  cx,
  cy,
  label,
  pulsing,
  opacity,
}) => {
  const frame = useCurrentFrame();

  // Pulse cycle: 30 frames, sinusoidal scale 1.0 → 1.3 → 1.0
  const pulsePhase = (frame % 30) / 30;
  const pulseScale = pulsing
    ? 1.0 + 0.3 * Math.sin(pulsePhase * Math.PI * 2)
    : 1.0;

  const isBold = label === 'Now';

  return (
    <div style={{ position: 'absolute', inset: 0, opacity }}>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Glow circle */}
        <circle
          cx={cx}
          cy={cy}
          r={24 * pulseScale}
          fill={COLORS.text}
          fillOpacity={OPACITIES.crossingGlow}
          filter="url(#crossingGlow)"
        />
        {/* Main circle */}
        <circle
          cx={cx}
          cy={cy}
          r={14 * pulseScale}
          fill="none"
          stroke={COLORS.text}
          strokeWidth={3}
          strokeOpacity={OPACITIES.crossingCircle}
        />
        {/* Inner dot */}
        <circle
          cx={cx}
          cy={cy}
          r={4 * pulseScale}
          fill={COLORS.text}
          fillOpacity={0.8}
        />
        {/* Glow filter */}
        <defs>
          <filter id="crossingGlow" x="-100%" y="-100%" width="300%" height="300%">
            <feGaussianBlur in="SourceGraphic" stdDeviation="12" />
          </filter>
        </defs>
      </svg>

      {/* Label */}
      <div
        style={{
          position: 'absolute',
          left: cx,
          top: cy - 40,
          transform: 'translateX(-50%)',
          fontFamily: 'Inter, sans-serif',
          fontSize: isBold ? 18 : 14,
          fontWeight: isBold ? 700 : 600,
          color: COLORS.text,
          whiteSpace: 'nowrap',
          textShadow: `0 0 12px rgba(226,232,240,0.4)`,
        }}
      >
        {label}
      </div>
    </div>
  );
};

export default CrossingPoint;
