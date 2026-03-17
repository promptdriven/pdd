import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  GRID_ROWS,
  GRID_COLS,
  GRID_SPACING,
  GRID_CENTER_X,
  GRID_CENTER_Y,
  GRID_LINE_COLOR,
  GRID_DOT_COLOR,
  ACTIVE_DOT_COLOR,
  NOZZLE_COLOR,
  LEFT_ACCENT,
  DIM_TEXT_COLOR,
  GRID_APPEAR_START,
  GRID_APPEAR_END,
  NOZZLE_START,
  NOZZLE_END,
  TOTAL_GRID_POINTS,
} from './constants';

/**
 * Left panel: 3D Printer coordinate grid with nozzle traversal.
 * Shows a grid that fills dot-by-dot as a nozzle moves across.
 */
export const CoordinateGrid: React.FC = () => {
  const frame = useCurrentFrame();

  // Grid origin (top-left of grid area)
  const gridW = (GRID_COLS - 1) * GRID_SPACING;
  const gridH = (GRID_ROWS - 1) * GRID_SPACING;
  const originX = GRID_CENTER_X - gridW / 2;
  const originY = GRID_CENTER_Y - gridH / 2;

  // Grid fade-in
  const gridOpacity = interpolate(
    frame,
    [GRID_APPEAR_START, GRID_APPEAR_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Nozzle traversal progress (0 → 1)
  const traversalProgress = interpolate(
    frame,
    [NOZZLE_START, NOZZLE_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Total points activated so far
  const activatedCount = Math.floor(traversalProgress * TOTAL_GRID_POINTS);

  // Nozzle position: row-by-row, snaking left-right-left
  const nozzlePointIndex = Math.min(activatedCount, TOTAL_GRID_POINTS - 1);
  const nozzleRow = Math.floor(nozzlePointIndex / GRID_COLS);
  const nozzleColRaw = nozzlePointIndex % GRID_COLS;
  const nozzleCol = nozzleRow % 2 === 0 ? nozzleColRaw : GRID_COLS - 1 - nozzleColRaw;
  const nozzleX = originX + nozzleCol * GRID_SPACING;
  const nozzleY = originY + nozzleRow * GRID_SPACING;

  // Counter value
  const counterValue = activatedCount;

  // Build grid lines (vertical + horizontal)
  const gridLines: React.ReactNode[] = [];
  for (let r = 0; r < GRID_ROWS; r++) {
    const y = originY + r * GRID_SPACING;
    gridLines.push(
      <line
        key={`h${r}`}
        x1={originX}
        y1={y}
        x2={originX + gridW}
        y2={y}
        stroke={GRID_LINE_COLOR}
        strokeOpacity={0.15}
        strokeWidth={1}
      />
    );
  }
  for (let c = 0; c < GRID_COLS; c++) {
    const x = originX + c * GRID_SPACING;
    gridLines.push(
      <line
        key={`v${c}`}
        x1={x}
        y1={originY}
        x2={x}
        y2={originY + gridH}
        stroke={GRID_LINE_COLOR}
        strokeOpacity={0.15}
        strokeWidth={1}
      />
    );
  }

  // Build dots
  const dots: React.ReactNode[] = [];
  for (let r = 0; r < GRID_ROWS; r++) {
    for (let c = 0; c < GRID_COLS; c++) {
      const x = originX + c * GRID_SPACING;
      const y = originY + r * GRID_SPACING;

      // Map (r, c) to snaking traversal index
      const traversalCol = r % 2 === 0 ? c : GRID_COLS - 1 - c;
      const traversalIndex = r * GRID_COLS + traversalCol;

      const isActive = traversalIndex < activatedCount;

      if (isActive) {
        // Animate scale-up for recently activated dots
        const activationFrame = NOZZLE_START + (traversalIndex / TOTAL_GRID_POINTS) * (NOZZLE_END - NOZZLE_START);
        const dotScale = interpolate(
          frame,
          [activationFrame, activationFrame + 3],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );
        dots.push(
          <circle
            key={`d${r}-${c}`}
            cx={x}
            cy={y}
            r={5 * dotScale}
            fill={ACTIVE_DOT_COLOR}
            opacity={0.8}
          />
        );
      } else {
        dots.push(
          <circle
            key={`d${r}-${c}`}
            cx={x}
            cy={y}
            r={3}
            fill={GRID_DOT_COLOR}
            opacity={0.3}
          />
        );
      }
    }
  }

  // Nozzle (inverted triangle)
  const showNozzle = frame >= NOZZLE_START && frame <= NOZZLE_END;
  const nozzleSize = 12;

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, width: 958, height: 1080 }}>
      <svg
        width={958}
        height={1080}
        viewBox="0 0 958 1080"
        style={{ opacity: gridOpacity }}
      >
        {/* Grid lines */}
        {gridLines}

        {/* Dots */}
        {dots}

        {/* Nozzle */}
        {showNozzle && (
          <polygon
            points={`${nozzleX - nozzleSize},${nozzleY - nozzleSize * 1.5} ${nozzleX + nozzleSize},${nozzleY - nozzleSize * 1.5} ${nozzleX},${nozzleY - 2}`}
            fill={NOZZLE_COLOR}
            opacity={0.6}
          />
        )}
      </svg>

      {/* Counter */}
      <div
        style={{
          position: 'absolute',
          bottom: 180,
          left: 0,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          color: LEFT_ACCENT,
        }}
      >
        Points specified: {counterValue}
      </div>

      {/* Annotation */}
      <div
        style={{
          position: 'absolute',
          bottom: 150,
          left: 0,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          color: DIM_TEXT_COLOR,
          opacity: 0.4,
        }}
      >
        Every point must be specified
      </div>
    </div>
  );
};

export default CoordinateGrid;
