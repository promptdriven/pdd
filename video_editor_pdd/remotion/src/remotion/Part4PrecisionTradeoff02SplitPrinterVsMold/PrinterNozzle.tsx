import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

const PRINTER_ACCENT = '#4A90D9';
const NOZZLE_COLOR = '#E2E8F0';
const DOT_SIZE = 6;
const TRAIL_OPACITY = 0.15;
const GRID_SPACING = 40;
const GRID_ORIGIN_X = 80;
const GRID_ORIGIN_Y = 80;
const GRID_COLS = 20;
const GRID_ROWS = 10;

interface GridPoint {
  x: number;
  y: number;
  col: number;
  row: number;
}

// Generate serpentine path
const NOZZLE_PATH: GridPoint[] = (() => {
  const points: GridPoint[] = [];
  for (let row = 0; row < GRID_ROWS; row++) {
    if (row % 2 === 0) {
      for (let col = 0; col < GRID_COLS; col++) {
        points.push({
          x: GRID_ORIGIN_X + col * GRID_SPACING,
          y: GRID_ORIGIN_Y + row * GRID_SPACING,
          col,
          row,
        });
      }
    } else {
      for (let col = GRID_COLS - 1; col >= 0; col--) {
        points.push({
          x: GRID_ORIGIN_X + col * GRID_SPACING,
          y: GRID_ORIGIN_Y + row * GRID_SPACING,
          col,
          row,
        });
      }
    }
  }
  return points;
})();

interface PrinterNozzleProps {
  panelWidth: number;
  panelHeight: number;
}

export const PrinterNozzle: React.FC<PrinterNozzleProps> = ({
  panelWidth,
  panelHeight,
}) => {
  const frame = useCurrentFrame();

  // Nozzle starts at frame 30, deposits over frames 30..390
  const depositFrames = 360; // frames 30-390
  const localFrame = Math.max(0, frame - 30);
  const totalPoints = NOZZLE_PATH.length;

  // How many points deposited so far (linear mechanical movement)
  const progress = Math.min(1, localFrame / depositFrames);
  const depositedCount = Math.floor(progress * totalPoints);

  // Current nozzle position — interpolate between last deposited and next
  const exactIndex = progress * totalPoints;
  const currentIndex = Math.min(Math.floor(exactIndex), totalPoints - 1);
  const nextIndex = Math.min(currentIndex + 1, totalPoints - 1);
  const subProgress = exactIndex - currentIndex;

  const nozzleX =
    NOZZLE_PATH[currentIndex].x +
    (NOZZLE_PATH[nextIndex].x - NOZZLE_PATH[currentIndex].x) * subProgress;
  const nozzleY =
    NOZZLE_PATH[currentIndex].y +
    (NOZZLE_PATH[nextIndex].y - NOZZLE_PATH[currentIndex].y) * subProgress;

  // Deposited dots
  const dots: React.ReactNode[] = [];
  for (let i = 0; i < depositedCount && i < totalPoints; i++) {
    const pt = NOZZLE_PATH[i];
    // Each dot scales in over 4 frames after deposit
    const depositFrame = (i / totalPoints) * depositFrames + 30;
    const dotAge = frame - depositFrame;
    const dotScale = interpolate(dotAge, [0, 4], [0, 1], {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });

    dots.push(
      <circle
        key={`dot-${i}`}
        cx={pt.x}
        cy={pt.y}
        r={(DOT_SIZE / 2) * dotScale}
        fill={PRINTER_ACCENT}
        opacity={0.6}
      />
    );
  }

  // Trail line connecting deposited points
  const trailPoints = NOZZLE_PATH.slice(0, depositedCount + 1);
  const trailPath =
    trailPoints.length > 1
      ? trailPoints.map((p, i) => `${i === 0 ? 'M' : 'L'} ${p.x} ${p.y}`).join(' ')
      : '';

  // Nozzle visibility
  const nozzleOpacity = frame >= 30 && frame <= 420 ? 1 : 0;

  return (
    <svg
      width={panelWidth}
      height={panelHeight}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Trail line */}
      {trailPath && (
        <path
          d={trailPath}
          stroke={PRINTER_ACCENT}
          strokeWidth={1}
          fill="none"
          opacity={TRAIL_OPACITY}
        />
      )}

      {/* Deposited dots */}
      {dots}

      {/* Nozzle — chevron pointing down */}
      {nozzleOpacity > 0 && (
        <g
          transform={`translate(${nozzleX}, ${nozzleY})`}
          opacity={nozzleOpacity}
        >
          <polygon
            points="-10,-14 10,-14 0,-2"
            fill={NOZZLE_COLOR}
          />
          <rect x={-1} y={-2} width={2} height={4} fill={NOZZLE_COLOR} />
        </g>
      )}
    </svg>
  );
};

export default PrinterNozzle;
