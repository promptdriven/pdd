import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { RED, GREEN, TEXT_SECONDARY, FONT_SANS, SPLIT_X, WIDTH } from './constants';

const TIMELINE_Y = 830;
const TIMELINE_HEIGHT = 90;
const PADDING_X = 60;
const HALF_WIDTH = (WIDTH - PADDING_X * 2) / 2 - 20;
const LEFT_START_X = PADDING_X;
const RIGHT_START_X = SPLIT_X + 20;

// Ratchet staircase steps
const RATCHET_STEPS = 6;

export const TimelineBar: React.FC<{ appearFrame: number }> = ({ appearFrame }) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [appearFrame, appearFrame + 60],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  const labelOpacity = interpolate(
    frame,
    [appearFrame + 40, appearFrame + 60],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  if (drawProgress <= 0) return null;

  // --- Left panel: Rising red line ---
  const redLinePoints: string[] = [];
  const redLineLength = HALF_WIDTH * drawProgress;
  const numRedPoints = 40;
  for (let i = 0; i <= numRedPoints; i++) {
    const t = i / numRedPoints;
    const x = LEFT_START_X + t * redLineLength;
    const y = TIMELINE_Y + TIMELINE_HEIGHT - t * TIMELINE_HEIGHT * 0.8 * Math.min(drawProgress, t <= drawProgress ? 1 : 0);
    if (x <= LEFT_START_X + redLineLength) {
      redLinePoints.push(`${x},${y}`);
    }
  }

  // --- Right panel: Green ratchet staircase ---
  const greenPathParts: string[] = [];
  const stepWidth = HALF_WIDTH / RATCHET_STEPS;
  const stepMaxHeight = TIMELINE_HEIGHT * 0.8;

  for (let i = 0; i < RATCHET_STEPS; i++) {
    const stepProgress = interpolate(
      drawProgress,
      [i / RATCHET_STEPS, (i + 0.5) / RATCHET_STEPS],
      [0, 1],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
    );

    if (stepProgress <= 0) break;

    const x = RIGHT_START_X + i * stepWidth;
    const nextX = x + stepWidth;
    const yBottom = TIMELINE_Y + TIMELINE_HEIGHT;
    const yStep = yBottom - ((i + 1) / RATCHET_STEPS) * stepMaxHeight;

    if (i === 0) {
      greenPathParts.push(`M ${x} ${yBottom}`);
    }
    // Vertical rise
    greenPathParts.push(`L ${x} ${yStep}`);
    // Horizontal hold
    greenPathParts.push(`L ${nextX * stepProgress + x * (1 - stepProgress)} ${yStep}`);
  }

  // Ratchet teeth (triangular notches)
  const teeth: React.ReactNode[] = [];
  for (let i = 0; i < RATCHET_STEPS; i++) {
    const stepAppear = interpolate(
      drawProgress,
      [(i + 0.3) / RATCHET_STEPS, (i + 0.6) / RATCHET_STEPS],
      [0, 1],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
    );
    if (stepAppear <= 0) continue;

    const x = RIGHT_START_X + i * stepWidth;
    const yBottom = TIMELINE_Y + TIMELINE_HEIGHT;
    const yStep = yBottom - ((i + 1) / RATCHET_STEPS) * stepMaxHeight;
    const toothSize = 6;

    teeth.push(
      <polygon
        key={`tooth-${i}`}
        points={`${x},${yStep} ${x - toothSize},${yStep + toothSize} ${x + toothSize},${yStep + toothSize}`}
        fill={GREEN}
        opacity={0.3 * stepAppear}
      />
    );
  }

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, width: WIDTH, height: 1080 }}>
      <svg width={WIDTH} height={1080} style={{ position: 'absolute', top: 0, left: 0 }}>
        {/* X-axis line */}
        <line
          x1={PADDING_X}
          y1={TIMELINE_Y + TIMELINE_HEIGHT}
          x2={WIDTH - PADDING_X}
          y2={TIMELINE_Y + TIMELINE_HEIGHT}
          stroke={TEXT_SECONDARY}
          strokeWidth={1}
          opacity={0.3 * drawProgress}
        />

        {/* Left: Rising red line */}
        {redLinePoints.length > 1 && (
          <polyline
            points={redLinePoints.join(' ')}
            fill="none"
            stroke={RED}
            strokeWidth={2}
            opacity={0.5}
          />
        )}

        {/* Right: Green ratchet staircase */}
        {greenPathParts.length > 0 && (
          <path
            d={greenPathParts.join(' ')}
            fill="none"
            stroke={GREEN}
            strokeWidth={2}
            opacity={0.5}
          />
        )}

        {/* Ratchet teeth */}
        {teeth}
      </svg>

      {/* TIME label */}
      <div
        style={{
          position: 'absolute',
          bottom: 1080 - TIMELINE_Y - TIMELINE_HEIGHT - 20,
          left: WIDTH / 2 - 40,
          width: 80,
          textAlign: 'center',
          fontFamily: FONT_SANS,
          fontSize: 10,
          color: TEXT_SECONDARY,
          opacity: 0.3 * drawProgress,
        }}
      >
        TIME →
      </div>

      {/* Left label: Patching effort */}
      <div
        style={{
          position: 'absolute',
          top: TIMELINE_Y - 5,
          left: LEFT_START_X + HALF_WIDTH - 120,
          fontFamily: FONT_SANS,
          fontSize: 10,
          color: RED,
          opacity: 0.5 * labelOpacity,
        }}
      >
        Patching effort ↑
      </div>

      {/* Right label: Test accumulation */}
      <div
        style={{
          position: 'absolute',
          top: TIMELINE_Y - 5,
          left: RIGHT_START_X + HALF_WIDTH - 140,
          fontFamily: FONT_SANS,
          fontSize: 10,
          color: GREEN,
          opacity: 0.5 * labelOpacity,
        }}
      >
        Test accumulation ↑
      </div>
    </div>
  );
};
