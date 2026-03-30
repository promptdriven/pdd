// WeAreHereLabel.tsx — "We are here." annotation with connector and pulsing glow
import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_TEXT_COLOR,
  LABEL_GLOW_COLOR,
  CONNECTOR_COLOR,
} from './constants';

interface WeAreHereLabelProps {
  /** X position of the crossing point to annotate */
  targetX: number;
  /** Y position of the crossing point to annotate */
  targetY: number;
  /** Frame when fade-in begins */
  fadeInStart: number;
  /** Duration of fade-in in frames */
  fadeInDuration: number;
}

export const WeAreHereLabel: React.FC<WeAreHereLabelProps> = ({
  targetX,
  targetY,
  fadeInStart,
  fadeInDuration,
}) => {
  const frame = useCurrentFrame();

  // Label position: offset to lower-right of target point
  const labelX = targetX + 40;
  const labelY = targetY + 55;

  // Fade in opacity
  const baseOpacity = interpolate(
    frame,
    [fadeInStart, fadeInStart + fadeInDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulsing glow — 60-frame cycle, opacity 0.8 to 1.0
  const pulsePhase = ((frame - fadeInStart) % 60) / 60;
  const pulseOpacity = interpolate(
    Math.sin(pulsePhase * Math.PI * 2),
    [-1, 1],
    [0.8, 1.0]
  );

  const combinedOpacity = baseOpacity * pulseOpacity;

  if (frame < fadeInStart) {
    return null;
  }

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      {/* Connector line from label to crossing point */}
      <line
        x1={labelX}
        y1={labelY - 12}
        x2={targetX}
        y2={targetY}
        stroke={CONNECTOR_COLOR}
        strokeWidth={1.5}
        opacity={baseOpacity * 0.3}
      />

      {/* Small circle at the crossing point */}
      <circle
        cx={targetX}
        cy={targetY}
        r={5}
        fill="none"
        stroke={CONNECTOR_COLOR}
        strokeWidth={1.5}
        opacity={baseOpacity * 0.5}
      />

      {/* Glow behind the text */}
      <rect
        x={labelX - 12}
        y={labelY - 20}
        width={180}
        height={36}
        rx={6}
        fill={LABEL_GLOW_COLOR}
        opacity={combinedOpacity * 0.1}
      />

      {/* "We are here." text */}
      <text
        x={labelX}
        y={labelY}
        fill={LABEL_TEXT_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={LABEL_FONT_SIZE}
        fontWeight={LABEL_FONT_WEIGHT}
        opacity={combinedOpacity}
      >
        We are here.
      </text>

      {/* Text shadow/glow layer */}
      <text
        x={labelX}
        y={labelY}
        fill={LABEL_GLOW_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={LABEL_FONT_SIZE}
        fontWeight={LABEL_FONT_WEIGHT}
        opacity={combinedOpacity * 0.15}
        filter="url(#text-glow)"
      />

      <defs>
        <filter id="text-glow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="4" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>
    </svg>
  );
};

export default WeAreHereLabel;
