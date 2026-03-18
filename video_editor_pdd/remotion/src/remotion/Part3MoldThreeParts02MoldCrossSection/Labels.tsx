import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MOLD_CX,
  MOLD_CY,
  CAVITY_W,
  CAVITY_H,
  MOLD_H,
  NOZZLE_TOP_W,
  AMBER,
  BLUE,
  GREEN,
  LABEL_SLATE,
  WALLS_START,
  WALLS_ILLUM_DUR,
  WALL_LABEL_STAGGER,
  NOZZLE_START,
  NOZZLE_ILLUM_DUR,
  NOZZLE_LABEL_STAGGER,
  CAVITY_START,
  CAVITY_FILL_DUR,
  CAVITY_LABEL_STAGGER,
  TITLE_START,
  TITLE_DUR,
  ALL_BRIGHT_START,
  ALL_BRIGHT_DUR,
  WALL_LABELS,
  NOZZLE_LABELS,
  CAVITY_LABELS,
  WIDTH,
  HEIGHT,
} from './constants';

// ── Shared label style helpers ─────────────────────────────

const fadeIn = (frame: number, startFrame: number, dur: number) =>
  interpolate(frame, [startFrame, startFrame + dur], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

// ── Section Title ──────────────────────────────────────────

export const SectionTitle: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = fadeIn(frame, TITLE_START, TITLE_DUR) * 0.4;

  return (
    <div
      style={{
        position: 'absolute',
        top: 100,
        left: 0,
        width: WIDTH,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: 12,
        fontWeight: 600,
        color: LABEL_SLATE,
        opacity,
        letterSpacing: 3,
        textTransform: 'uppercase',
      }}
    >
      THREE TYPES OF CAPITAL
    </div>
  );
};

// ── Wall Labels with callout arrows ────────────────────────

export const WallLabels: React.FC = () => {
  const frame = useCurrentFrame();

  const cavLeft = MOLD_CX - CAVITY_W / 2;
  const cavRight = MOLD_CX + CAVITY_W / 2;
  const cavTop = MOLD_CY - CAVITY_H / 2 + 30;
  const cavBot = cavTop + CAVITY_H;

  // Dim when nozzle activates, re-brighten at end
  const dimFactor = interpolate(
    frame,
    [NOZZLE_START, NOZZLE_START + 15, ALL_BRIGHT_START, ALL_BRIGHT_START + ALL_BRIGHT_DUR],
    [1, 0.3, 0.3, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const labels = WALL_LABELS.map((label, i) => {
    const labelStart = WALLS_START + WALLS_ILLUM_DUR + i * WALL_LABEL_STAGGER;
    const progress = fadeIn(frame, labelStart, 15);

    // Arrow draw progress
    const arrowProgress = interpolate(frame, [labelStart, labelStart + 12], [0, 1], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.bezier(0.25, 0.1, 0.25, 1)),
    });

    let textX: number;
    let textY: number;
    let anchorX: number;
    let anchorY: number;
    let textAnchor: string;

    if (label.side === 'left') {
      anchorX = cavLeft;
      anchorY = MOLD_CY + label.yOffset;
      textX = cavLeft - 140;
      textY = anchorY;
      textAnchor = 'end';
    } else if (label.side === 'right') {
      anchorX = cavRight;
      anchorY = MOLD_CY + label.yOffset;
      textX = cavRight + 140;
      textY = anchorY;
      textAnchor = 'start';
    } else {
      // bottom
      anchorX = MOLD_CX;
      anchorY = cavBot;
      textX = MOLD_CX;
      textY = cavBot + 50;
      textAnchor = 'middle';
    }

    return (
      <g key={label.text} opacity={progress * dimFactor}>
        {/* Callout arrow line */}
        <line
          x1={anchorX}
          y1={anchorY}
          x2={anchorX + (textX - anchorX) * arrowProgress}
          y2={anchorY + (textY - anchorY) * arrowProgress}
          stroke={AMBER}
          strokeWidth={1}
          opacity={0.3}
        />
        {/* Small dot at anchor point */}
        <circle cx={anchorX} cy={anchorY} r={2.5} fill={AMBER} opacity={0.5 * arrowProgress} />
        {/* Label text */}
        <text
          x={textX}
          y={textY + 3}
          fill={AMBER}
          opacity={0.7}
          fontFamily="'JetBrains Mono', monospace"
          fontSize={9}
          textAnchor={textAnchor}
        >
          {label.text}
        </text>
      </g>
    );
  });

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      {labels}
    </svg>
  );
};

// ── Nozzle Labels ──────────────────────────────────────────

export const NozzleLabels: React.FC = () => {
  const frame = useCurrentFrame();

  const shellTop = MOLD_CY - MOLD_H / 2;
  const nozTopY = shellTop - 10;

  // Dim when cavity activates, re-brighten at end
  const dimFactor = interpolate(
    frame,
    [CAVITY_START, CAVITY_START + 15, ALL_BRIGHT_START, ALL_BRIGHT_START + ALL_BRIGHT_DUR],
    [1, 0.3, 0.3, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const positions = [
    { x: MOLD_CX - NOZZLE_TOP_W - 30, anchor: 'end' },   // intent — left
    { x: MOLD_CX, anchor: 'middle' },                       // requirements — center
    { x: MOLD_CX + NOZZLE_TOP_W + 30, anchor: 'start' },  // constraints — right
  ];

  const labels = NOZZLE_LABELS.map((text, i) => {
    const labelStart = NOZZLE_START + NOZZLE_ILLUM_DUR + i * NOZZLE_LABEL_STAGGER;
    const progress = fadeIn(frame, labelStart, 15);

    const { x, anchor } = positions[i];
    const y = nozTopY - 20;

    return (
      <g key={text} opacity={progress * dimFactor}>
        {/* Small connector line */}
        <line
          x1={x}
          y1={y + 8}
          x2={x}
          y2={nozTopY - 2}
          stroke={BLUE}
          strokeWidth={0.75}
          opacity={0.3}
        />
        <text
          x={x}
          y={y}
          fill={BLUE}
          opacity={0.7}
          fontFamily="Inter, sans-serif"
          fontSize={11}
          textAnchor={anchor}
        >
          {text}
        </text>
      </g>
    );
  });

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      {labels}
    </svg>
  );
};

// ── Cavity Labels ──────────────────────────────────────────

export const CavityLabels: React.FC = () => {
  const frame = useCurrentFrame();

  const cavLeft = MOLD_CX - CAVITY_W / 2;
  const cavTop = MOLD_CY - CAVITY_H / 2 + 30;

  const positionMap: Record<string, { x: number; y: number; anchor: string }> = {
    'upper-left': { x: cavLeft + 60, y: cavTop + 80, anchor: 'start' },
    center: { x: MOLD_CX, y: MOLD_CY + 40, anchor: 'middle' },
    'lower-right': { x: cavLeft + CAVITY_W - 60, y: cavTop + CAVITY_H - 60, anchor: 'end' },
  };

  const labels = CAVITY_LABELS.map((label, i) => {
    const labelStart = CAVITY_START + CAVITY_FILL_DUR * 0.5 + i * CAVITY_LABEL_STAGGER;
    const progress = fadeIn(frame, labelStart, 15);

    const pos = positionMap[label.position];

    return (
      <g key={label.text} opacity={progress}>
        <text
          x={pos.x}
          y={pos.y}
          fill={GREEN}
          opacity={0.6}
          fontFamily="Inter, sans-serif"
          fontSize={11}
          textAnchor={pos.anchor}
        >
          {label.text}
        </text>
      </g>
    );
  });

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
    >
      {labels}
    </svg>
  );
};
