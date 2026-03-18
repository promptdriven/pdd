import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  GRID_X,
  GRID_Y,
  GRID_W,
  GRID_H,
  GRID_CENTER_X,
  GRID_CENTER_Y,
  BORDER_COLOR,
  GREEN,
  RED,
} from './constants';

interface QuadrantGridProps {
  startFrame: number;
  drawDuration: number;
}

/**
 * Draws the 2×2 grid border, cross dividers, axis labels, and arrow indicators.
 * Animates the grid drawing in from the center outward.
 */
export const QuadrantGrid: React.FC<QuadrantGridProps> = ({
  startFrame,
  drawDuration,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  // Draw progress: 0 → 1
  const draw = interpolate(localFrame, [0, drawDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Label fade-in (starts at 50% of draw, finishes at 100%)
  const labelAlpha = interpolate(
    localFrame,
    [drawDuration * 0.5, drawDuration],
    [0, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Outer border grows from center
  const halfW = (GRID_W / 2) * draw;
  const halfH = (GRID_H / 2) * draw;
  const borderLeft = GRID_CENTER_X - halfW;
  const borderTop = GRID_CENTER_Y - halfH;
  const borderWidth = halfW * 2;
  const borderHeight = halfH * 2;

  // Cross dividers grow from center
  const vertLineTop = GRID_CENTER_Y - halfH;
  const vertLineBottom = GRID_CENTER_Y + halfH;
  const horizLineLeft = GRID_CENTER_X - halfW;
  const horizLineRight = GRID_CENTER_X + halfW;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: '100%',
        height: '100%',
        pointerEvents: 'none',
      }}
    >
      {/* SVG for grid lines */}
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', left: 0, top: 0 }}
      >
        {/* Outer border */}
        <rect
          x={borderLeft}
          y={borderTop}
          width={borderWidth}
          height={borderHeight}
          fill="none"
          stroke={BORDER_COLOR}
          strokeOpacity={0.3}
          strokeWidth={2}
        />
        {/* Vertical divider */}
        <line
          x1={GRID_CENTER_X}
          y1={vertLineTop}
          x2={GRID_CENTER_X}
          y2={vertLineBottom}
          stroke={BORDER_COLOR}
          strokeOpacity={0.2}
          strokeWidth={1}
        />
        {/* Horizontal divider */}
        <line
          x1={horizLineLeft}
          y1={GRID_CENTER_Y}
          x2={horizLineRight}
          y2={GRID_CENTER_Y}
          stroke={BORDER_COLOR}
          strokeOpacity={0.2}
          strokeWidth={1}
        />

        {/* X-axis arrow (below grid) */}
        <defs>
          <linearGradient id="xAxisGrad" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor={GREEN} stopOpacity={0.3 * draw} />
            <stop offset="100%" stopColor={RED} stopOpacity={0.3 * draw} />
          </linearGradient>
          <linearGradient id="yAxisGrad" x1="0%" y1="0%" x2="0%" y2="100%">
            <stop offset="0%" stopColor={GREEN} stopOpacity={0.3 * draw} />
            <stop offset="100%" stopColor={RED} stopOpacity={0.3 * draw} />
          </linearGradient>
        </defs>
        {/* X-axis arrow line */}
        <line
          x1={GRID_X + 20}
          y1={GRID_Y + GRID_H + 30}
          x2={GRID_X + GRID_W - 20}
          y2={GRID_Y + GRID_H + 30}
          stroke="url(#xAxisGrad)"
          strokeWidth={1.5}
          opacity={draw}
        />
        {/* X-axis arrowhead */}
        <polygon
          points={`${GRID_X + GRID_W - 20},${GRID_Y + GRID_H + 26} ${GRID_X + GRID_W - 20},${GRID_Y + GRID_H + 34} ${GRID_X + GRID_W - 10},${GRID_Y + GRID_H + 30}`}
          fill={RED}
          opacity={0.3 * draw}
        />

        {/* Y-axis arrow line */}
        <line
          x1={GRID_X - 30}
          y1={GRID_Y + 20}
          x2={GRID_X - 30}
          y2={GRID_Y + GRID_H - 20}
          stroke="url(#yAxisGrad)"
          strokeWidth={1.5}
          opacity={draw}
        />
        {/* Y-axis arrowhead */}
        <polygon
          points={`${GRID_X - 34},${GRID_Y + GRID_H - 20} ${GRID_X - 26},${GRID_Y + GRID_H - 20} ${GRID_X - 30},${GRID_Y + GRID_H - 10}`}
          fill={RED}
          opacity={0.3 * draw}
        />
      </svg>

      {/* Axis Labels */}
      {/* X-axis: Greenfield (left) */}
      <div
        style={{
          position: 'absolute',
          left: GRID_X,
          top: GRID_Y + GRID_H + 40,
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: GREEN,
          opacity: labelAlpha,
        }}
      >
        Greenfield
      </div>
      {/* X-axis: Brownfield (right) */}
      <div
        style={{
          position: 'absolute',
          right: 1920 - (GRID_X + GRID_W),
          top: GRID_Y + GRID_H + 40,
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: RED,
          opacity: labelAlpha,
          textAlign: 'right',
        }}
      >
        Brownfield
      </div>
      {/* Y-axis: In-Distribution (top) */}
      <div
        style={{
          position: 'absolute',
          left: GRID_X - 50,
          top: GRID_Y - 8,
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: GREEN,
          opacity: labelAlpha,
          transformOrigin: 'center center',
          transform: 'rotate(-90deg)',
          whiteSpace: 'nowrap',
        }}
      >
        In-Distribution
      </div>
      {/* Y-axis: Out-of-Distribution (bottom) */}
      <div
        style={{
          position: 'absolute',
          left: GRID_X - 70,
          bottom: 1080 - (GRID_Y + GRID_H) + 8,
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: RED,
          opacity: labelAlpha,
          transformOrigin: 'center center',
          transform: 'rotate(-90deg)',
          whiteSpace: 'nowrap',
        }}
      >
        Out-of-Distribution
      </div>
    </div>
  );
};

export default QuadrantGrid;
