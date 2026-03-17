import React from 'react';
import {
  CENTER_X,
  CENTER_Y,
  MOLD_WIDTH,
  CAVITY_WIDTH,
  CAVITY_HEIGHT,
  NOZZLE_HEIGHT,
  AMBER,
  BLUE,
  GREEN,
  WALL_LABELS,
  NOZZLE_LABELS,
  CAVITY_LABELS,
} from './constants';

// ── Wall Labels with callout arrows ─────────────────

interface WallLabelsProps {
  opacity: number; // 0..1 controls label visibility
  arrowProgress: number; // 0..1 per-label draw progress (staggered externally)
  labelProgresses: number[]; // per-label opacity [0..1]
}

export const WallLabels: React.FC<WallLabelsProps> = ({
  opacity,
  arrowProgress,
  labelProgresses,
}) => {
  if (opacity <= 0) return null;

  const cavityLeft = CENTER_X - CAVITY_WIDTH / 2;
  const cavityRight = CENTER_X + CAVITY_WIDTH / 2;
  const cavityTop = CENTER_Y - CAVITY_HEIGHT / 2;
  const cavityBottom = CENTER_Y + CAVITY_HEIGHT / 2;

  const labelPositions = WALL_LABELS.map((label, i) => {
    if (label.side === 'left') {
      const y = CENTER_Y + label.yOffset;
      return {
        ...label,
        labelX: cavityLeft - 160,
        labelY: y,
        arrowX1: cavityLeft - 10,
        arrowY1: y,
        arrowX2: cavityLeft - 150,
        arrowY2: y,
        textAnchor: 'end' as const,
      };
    }
    if (label.side === 'right') {
      const y = CENTER_Y + label.yOffset;
      return {
        ...label,
        labelX: cavityRight + 160,
        labelY: y,
        arrowX1: cavityRight + 10,
        arrowY1: y,
        arrowX2: cavityRight + 150,
        arrowY2: y,
        textAnchor: 'start' as const,
      };
    }
    // bottom
    return {
      ...label,
      labelX: CENTER_X,
      labelY: cavityBottom + 60,
      arrowX1: CENTER_X,
      arrowY1: cavityBottom + 10,
      arrowX2: CENTER_X,
      arrowY2: cavityBottom + 45,
      textAnchor: 'middle' as const,
    };
  });

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {labelPositions.map((lp, i) => {
        const lProgress = labelProgresses[i] ?? 0;
        const aProgress = Math.min(1, arrowProgress);
        if (lProgress <= 0) return null;

        const arrowLen = Math.hypot(
          lp.arrowX2 - lp.arrowX1,
          lp.arrowY2 - lp.arrowY1
        );

        return (
          <g key={i} opacity={opacity}>
            {/* Callout arrow */}
            <line
              x1={lp.arrowX1}
              y1={lp.arrowY1}
              x2={lp.arrowX2}
              y2={lp.arrowY2}
              stroke={AMBER}
              strokeWidth={1}
              opacity={0.3 * lProgress}
              strokeDasharray={arrowLen}
              strokeDashoffset={arrowLen * (1 - aProgress * lProgress)}
            />
            {/* Small dot at wall end */}
            <circle
              cx={lp.arrowX1}
              cy={lp.arrowY1}
              r={3}
              fill={AMBER}
              opacity={0.4 * lProgress}
            />
            {/* Label text */}
            <text
              x={lp.labelX}
              y={lp.labelY + 4}
              fill={AMBER}
              opacity={0.7 * lProgress}
              fontSize={9}
              fontFamily="'JetBrains Mono', monospace"
              textAnchor={lp.textAnchor}
            >
              {lp.text}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

// ── Nozzle Labels ───────────────────────────────────

interface NozzleLabelsProps {
  opacity: number;
  labelProgresses: number[]; // per-label 0..1
}

export const NozzleLabels: React.FC<NozzleLabelsProps> = ({
  opacity,
  labelProgresses,
}) => {
  if (opacity <= 0) return null;

  const moldTop = CENTER_Y - 350; // MOLD_HEIGHT/2
  const nozzleTopY = moldTop - NOZZLE_HEIGHT;

  const positions = [
    { x: CENTER_X - 100, y: nozzleTopY - 30 }, // intent — left
    { x: CENTER_X, y: nozzleTopY - 50 },         // requirements — center
    { x: CENTER_X + 100, y: nozzleTopY - 30 },   // constraints — right
  ];

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {NOZZLE_LABELS.map((label, i) => {
        const p = labelProgresses[i] ?? 0;
        if (p <= 0) return null;
        return (
          <text
            key={i}
            x={positions[i].x}
            y={positions[i].y}
            fill={BLUE}
            opacity={0.7 * p * opacity}
            fontSize={11}
            fontFamily="Inter, sans-serif"
            textAnchor="middle"
          >
            {label}
          </text>
        );
      })}
    </svg>
  );
};

// ── Cavity Labels ───────────────────────────────────

interface CavityLabelsProps {
  opacity: number;
  labelProgresses: number[]; // per-label 0..1
}

export const CavityLabels: React.FC<CavityLabelsProps> = ({
  opacity,
  labelProgresses,
}) => {
  if (opacity <= 0) return null;

  const cavityLeft = CENTER_X - CAVITY_WIDTH / 2;
  const cavityTop = CENTER_Y - CAVITY_HEIGHT / 2;

  const positions = CAVITY_LABELS.map((label) => {
    switch (label.position) {
      case 'upper-left':
        return { x: cavityLeft + 80, y: cavityTop + 100 };
      case 'center':
        return { x: CENTER_X, y: CENTER_Y + 20 };
      case 'lower-right':
        return {
          x: cavityLeft + CAVITY_WIDTH - 80,
          y: cavityTop + CAVITY_HEIGHT - 80,
        };
      default:
        return { x: CENTER_X, y: CENTER_Y };
    }
  });

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {CAVITY_LABELS.map((label, i) => {
        const p = labelProgresses[i] ?? 0;
        if (p <= 0) return null;
        return (
          <text
            key={i}
            x={positions[i].x}
            y={positions[i].y}
            fill={GREEN}
            opacity={0.6 * p * opacity}
            fontSize={11}
            fontFamily="Inter, sans-serif"
            textAnchor="middle"
            fontWeight={500}
          >
            {label.text}
          </text>
        );
      })}
    </svg>
  );
};
