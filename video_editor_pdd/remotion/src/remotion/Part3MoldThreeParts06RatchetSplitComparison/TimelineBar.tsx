import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  RED,
  GREEN,
  TEXT_MUTED,
  SPLIT_X,
  TIMELINE_Y,
  TIMELINE_MARGIN_X,
  FRAME,
  RATCHET_STEPS,
} from './constants';

// ── Rising red line (left side) ──
const RisingLine: React.FC<{ progress: number }> = ({ progress }) => {
  const startX = TIMELINE_MARGIN_X;
  const endX = SPLIT_X - 40;
  const lineWidth = (endX - startX) * progress;
  const topY = 10;
  const bottomY = 80;

  // Line rises from bottom-left to top-right
  const currentY = bottomY - (bottomY - topY) * progress;

  return (
    <g>
      {/* Axis line */}
      <line x1={startX} y1={bottomY} x2={endX} y2={bottomY} stroke={TEXT_MUTED} strokeWidth={1} opacity={0.3} />
      {/* Rising line */}
      <line
        x1={startX}
        y1={bottomY}
        x2={startX + lineWidth}
        y2={currentY}
        stroke={RED}
        strokeWidth={2}
        opacity={0.5}
      />
      {/* Label */}
      {progress > 0.5 && (
        <text
          x={startX + lineWidth + 6}
          y={currentY + 4}
          fill={RED}
          fontSize={10}
          fontFamily="Inter, sans-serif"
          opacity={0.6}
        >
          Patching effort
        </text>
      )}
    </g>
  );
};

// ── Ratchet staircase (right side) ──
const RatchetStaircase: React.FC<{ progress: number }> = ({ progress }) => {
  const startX = SPLIT_X + 40;
  const endX = 1920 - TIMELINE_MARGIN_X;
  const stepWidth = (endX - startX) / RATCHET_STEPS;
  const topY = 10;
  const bottomY = 80;
  const stepHeight = (bottomY - topY) / RATCHET_STEPS;

  const stepsVisible = Math.floor(progress * RATCHET_STEPS);
  const partialStep = (progress * RATCHET_STEPS) % 1;

  const pathPoints: string[] = [];
  pathPoints.push(`M ${startX} ${bottomY}`);

  for (let i = 0; i < stepsVisible; i++) {
    const x1 = startX + i * stepWidth;
    const x2 = startX + (i + 1) * stepWidth;
    const y = bottomY - (i + 1) * stepHeight;
    // Horizontal then vertical (staircase)
    pathPoints.push(`L ${x2} ${bottomY - i * stepHeight}`);
    pathPoints.push(`L ${x2} ${y}`);
  }

  // Partial step
  if (stepsVisible < RATCHET_STEPS && partialStep > 0) {
    const x1 = startX + stepsVisible * stepWidth;
    const partialX = x1 + stepWidth * partialStep;
    const currentFloorY = bottomY - stepsVisible * stepHeight;
    pathPoints.push(`L ${partialX} ${currentFloorY}`);
  }

  // Ratchet teeth (small triangles on each step)
  const teeth: React.ReactElement[] = [];
  for (let i = 0; i < stepsVisible; i++) {
    const tx = startX + (i + 1) * stepWidth;
    const ty = bottomY - (i + 1) * stepHeight;
    teeth.push(
      <polygon
        key={i}
        points={`${tx - 4},${ty} ${tx},${ty - 6} ${tx + 4},${ty}`}
        fill={GREEN}
        opacity={0.3}
      />
    );
  }

  return (
    <g>
      {/* Axis line */}
      <line x1={startX} y1={bottomY} x2={endX} y2={bottomY} stroke={TEXT_MUTED} strokeWidth={1} opacity={0.3} />
      {/* Staircase path */}
      <path
        d={pathPoints.join(' ')}
        fill="none"
        stroke={GREEN}
        strokeWidth={2}
        opacity={0.5}
      />
      {/* Teeth */}
      {teeth}
      {/* Label */}
      {stepsVisible >= 3 && (
        <text
          x={endX - 110}
          y={topY - 2}
          fill={GREEN}
          fontSize={10}
          fontFamily="Inter, sans-serif"
          opacity={0.6}
        >
          Test accumulation
        </text>
      )}
    </g>
  );
};

// ── Full Timeline Bar ──
export const TimelineBar: React.FC = () => {
  const frame = useCurrentFrame();

  // Progress of timeline drawing
  const progress = interpolate(
    frame,
    [FRAME.TIMELINE_START, FRAME.TIMELINE_START + FRAME.TIMELINE_DRAW_DUR],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Fade in
  const opacity = interpolate(
    frame,
    [FRAME.TIMELINE_START, FRAME.TIMELINE_START + 15],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  if (frame < FRAME.TIMELINE_START) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: TIMELINE_Y,
        width: 1920,
        height: 100,
        opacity,
      }}
    >
      <svg width={1920} height={100} viewBox="0 0 1920 100">
        {/* "OVER TIME" center label */}
        <text
          x={960}
          y={96}
          textAnchor="middle"
          fill={TEXT_MUTED}
          fontSize={10}
          fontFamily="Inter, sans-serif"
          opacity={0.3}
        >
          TIME →
        </text>

        <RisingLine progress={progress} />
        <RatchetStaircase progress={progress} />
      </svg>
    </div>
  );
};

export default TimelineBar;
