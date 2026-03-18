import React from 'react';
import { AbsoluteFill, Easing, interpolate, useCurrentFrame } from 'remotion';
import { GHOST_ELEMENTS, TIMING } from './constants';

/**
 * Renders one of the three ghost shapes (wall, nozzle, material)
 * with stroke-draw animation and gentle pulse.
 */
const GhostShape: React.FC<{
  shape: 'wall' | 'nozzle' | 'material';
  color: string;
  x: number;
  y: number;
  label: string;
  drawProgress: number;
  pulseOpacity: number;
}> = ({ shape, color, x, y, label, drawProgress, pulseOpacity }) => {
  const baseOpacity = 0.04 + pulseOpacity;
  const glowOpacity = 0.02 + pulseOpacity * 0.5;
  const labelOpacity = 0.03;

  const filterId = `glow-${shape}`;

  return (
    <g>
      {/* Glow filter */}
      <defs>
        <filter id={filterId} x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="8" result="blur" />
          <feFlood floodColor={color} floodOpacity={glowOpacity} result="color" />
          <feComposite in="color" in2="blur" operator="in" result="glow" />
          <feMerge>
            <feMergeNode in="glow" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {shape === 'wall' && (
        <WallShape
          x={x}
          y={y}
          color={color}
          opacity={baseOpacity}
          drawProgress={drawProgress}
          filterId={filterId}
        />
      )}
      {shape === 'nozzle' && (
        <NozzleShape
          x={x}
          y={y}
          color={color}
          opacity={baseOpacity}
          drawProgress={drawProgress}
          filterId={filterId}
        />
      )}
      {shape === 'material' && (
        <MaterialShape
          x={x}
          y={y}
          color={color}
          opacity={baseOpacity}
          drawProgress={drawProgress}
          filterId={filterId}
        />
      )}

      {/* Label beneath shape */}
      <text
        x={x}
        y={y + 80}
        textAnchor="middle"
        fontFamily="Inter, sans-serif"
        fontSize={8}
        fill={color}
        opacity={labelOpacity * drawProgress}
        letterSpacing={2}
      >
        {label}
      </text>
    </g>
  );
};

/** Wall segment — stacked rectangular blocks */
const WallShape: React.FC<{
  x: number;
  y: number;
  color: string;
  opacity: number;
  drawProgress: number;
  filterId: string;
}> = ({ x, y, color, opacity, drawProgress, filterId }) => {
  // Three stacked blocks
  const blockWidth = 80;
  const blockHeight = 20;
  const gap = 4;
  const totalPathLength = 3 * 2 * (blockWidth + blockHeight);

  return (
    <g filter={`url(#${filterId})`}>
      {[0, 1, 2].map((i) => {
        const by = y - 30 + i * (blockHeight + gap);
        const bx = x - blockWidth / 2 + (i % 2 === 1 ? 10 : -10);
        const perimeter = 2 * (blockWidth + blockHeight);
        const dashOffset = perimeter * (1 - drawProgress);
        return (
          <rect
            key={i}
            x={bx}
            y={by}
            width={blockWidth}
            height={blockHeight}
            fill="none"
            stroke={color}
            strokeWidth={2}
            opacity={opacity}
            strokeDasharray={perimeter}
            strokeDashoffset={dashOffset}
          />
        );
      })}
    </g>
  );
};

/** Injection nozzle — tapered funnel shape */
const NozzleShape: React.FC<{
  x: number;
  y: number;
  color: string;
  opacity: number;
  drawProgress: number;
  filterId: string;
}> = ({ x, y, color, opacity, drawProgress, filterId }) => {
  // Funnel: wide top narrowing to bottom
  const pathD = `
    M ${x - 40} ${y - 30}
    L ${x + 40} ${y - 30}
    L ${x + 12} ${y + 30}
    L ${x - 12} ${y + 30}
    Z
  `;
  // Nozzle tip
  const tipD = `
    M ${x - 8} ${y + 30}
    L ${x - 8} ${y + 50}
    L ${x + 8} ${y + 50}
    L ${x + 8} ${y + 30}
  `;
  const pathLen = 240;
  const tipLen = 56;

  return (
    <g filter={`url(#${filterId})`}>
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={2}
        opacity={opacity}
        strokeDasharray={pathLen}
        strokeDashoffset={pathLen * (1 - drawProgress)}
      />
      <path
        d={tipD}
        fill="none"
        stroke={color}
        strokeWidth={2}
        opacity={opacity}
        strokeDasharray={tipLen}
        strokeDashoffset={tipLen * (1 - drawProgress)}
      />
    </g>
  );
};

/** Material swatch — organic flowing shape */
const MaterialShape: React.FC<{
  x: number;
  y: number;
  color: string;
  opacity: number;
  drawProgress: number;
  filterId: string;
}> = ({ x, y, color, opacity, drawProgress, filterId }) => {
  // Organic blob using cubic bezier
  const pathD = `
    M ${x - 40} ${y}
    C ${x - 40} ${y - 35}, ${x - 15} ${y - 50}, ${x} ${y - 40}
    C ${x + 15} ${y - 50}, ${x + 45} ${y - 30}, ${x + 40} ${y}
    C ${x + 45} ${y + 30}, ${x + 15} ${y + 50}, ${x} ${y + 40}
    C ${x - 15} ${y + 50}, ${x - 40} ${y + 35}, ${x - 40} ${y}
    Z
  `;
  // Internal wavy lines for texture
  const wave1 = `M ${x - 25} ${y - 10} Q ${x} ${y - 25}, ${x + 25} ${y - 10}`;
  const wave2 = `M ${x - 25} ${y + 10} Q ${x} ${y - 5}, ${x + 25} ${y + 10}`;
  const pathLen = 320;
  const waveLen = 80;

  return (
    <g filter={`url(#${filterId})`}>
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={2}
        opacity={opacity}
        strokeDasharray={pathLen}
        strokeDashoffset={pathLen * (1 - drawProgress)}
      />
      <path
        d={wave1}
        fill="none"
        stroke={color}
        strokeWidth={1}
        opacity={opacity * 0.6}
        strokeDasharray={waveLen}
        strokeDashoffset={waveLen * (1 - drawProgress)}
      />
      <path
        d={wave2}
        fill="none"
        stroke={color}
        strokeWidth={1}
        opacity={opacity * 0.6}
        strokeDasharray={waveLen}
        strokeDashoffset={waveLen * (1 - drawProgress)}
      />
    </g>
  );
};

/** Container for all three ghost shapes with draw + pulse animation */
export const GhostShapes: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - TIMING.GHOST_DRAW_START;
  if (localFrame < 0) return null;

  // Stroke draw progress: 0 → 1 over GHOST_DRAW_DURATION frames
  const drawProgress = interpolate(
    localFrame,
    [0, TIMING.GHOST_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Gentle pulse after shapes are drawn (sine wave on 30-frame cycle)
  const pulsePhase = ((localFrame - TIMING.GHOST_DRAW_DURATION) / TIMING.PULSE_CYCLE) * Math.PI * 2;
  const pulseActive = localFrame > TIMING.GHOST_DRAW_DURATION;
  const pulseValue = pulseActive
    ? interpolate(Math.sin(pulsePhase), [-1, 1], [0, 0.015])
    : 0;

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {GHOST_ELEMENTS.map((el) => (
          <GhostShape
            key={el.shape}
            shape={el.shape}
            color={el.color}
            x={el.x}
            y={el.y}
            label={el.label}
            drawProgress={drawProgress}
            pulseOpacity={pulseValue}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};
