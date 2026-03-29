import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  PANEL_WIDTH,
  CANVAS_HEIGHT,
  NOZZLE_COLOR,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  DOT_COLOR,
  DOT_OPACITY,
  DOT_SIZE,
  TRAIL_COLOR,
  TRAIL_OPACITY,
  PHASE_ANIMATE_START,
  PHASE_COMPLETE,
  generateNozzlePath,
} from './constants';

const nozzlePath = generateNozzlePath();
const TOTAL_POINTS = nozzlePath.length;
// Nozzle deposits from frame 30 to frame 420 (390 frames)
const DEPOSIT_FRAMES = PHASE_COMPLETE - PHASE_ANIMATE_START;

export const PrinterNozzle: React.FC = () => {
  const frame = useCurrentFrame();

  // How far through the deposition are we (0 to TOTAL_POINTS)
  const depositProgress = interpolate(
    frame,
    [PHASE_ANIMATE_START, PHASE_COMPLETE],
    [0, TOTAL_POINTS],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const currentPointIndex = Math.min(Math.floor(depositProgress), TOTAL_POINTS - 1);
  const currentPoint = nozzlePath[currentPointIndex];

  // Deposited dots
  const dots: React.ReactNode[] = [];
  const trailSegments: React.ReactNode[] = [];

  for (let i = 0; i <= currentPointIndex; i++) {
    const pt = nozzlePath[i];
    // Each dot appears at its specific frame
    const dotFrame = PHASE_ANIMATE_START + (i / TOTAL_POINTS) * DEPOSIT_FRAMES;
    const dotAge = frame - dotFrame;
    const dotScale = interpolate(dotAge, [0, 4], [0, 1], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    });

    dots.push(
      <circle
        key={`dot-${i}`}
        cx={pt.x}
        cy={pt.y}
        r={(DOT_SIZE / 2) * dotScale}
        fill={DOT_COLOR}
        fillOpacity={DOT_OPACITY}
      />
    );

    // Trail line connecting dots
    if (i > 0) {
      const prevPt = nozzlePath[i - 1];
      trailSegments.push(
        <line
          key={`trail-${i}`}
          x1={prevPt.x}
          y1={prevPt.y}
          x2={pt.x}
          y2={pt.y}
          stroke={TRAIL_COLOR}
          strokeOpacity={TRAIL_OPACITY}
          strokeWidth={1}
        />
      );
    }
  }

  // Only render nozzle if we've started depositing
  const showNozzle = frame >= PHASE_ANIMATE_START && frame < PHASE_COMPLETE + 30;

  return (
    <svg
      width={PANEL_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Trail lines */}
      {trailSegments}

      {/* Deposited dots */}
      {dots}

      {/* Nozzle head (chevron/triangle pointing down) */}
      {showNozzle && currentPoint && (
        <polygon
          points={`
            ${currentPoint.x},${currentPoint.y - NOZZLE_HEIGHT - 4}
            ${currentPoint.x - NOZZLE_WIDTH / 2},${currentPoint.y - NOZZLE_HEIGHT - 4 - NOZZLE_HEIGHT}
            ${currentPoint.x + NOZZLE_WIDTH / 2},${currentPoint.y - NOZZLE_HEIGHT - 4 - NOZZLE_HEIGHT}
          `}
          fill={NOZZLE_COLOR}
          opacity={0.9}
        />
      )}
    </svg>
  );
};

export default PrinterNozzle;
