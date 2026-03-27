import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  MOLD_STROKE_COLOR,
  MOLD_STROKE_WIDTH,
  WALL_COLOR,
  DIMMED_OPACITY,
  MOLD_OUTER_WIDTH,
  MOLD_OUTER_HEIGHT,
  MOLD_INNER_WIDTH,
  MOLD_INNER_HEIGHT,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  ZOOM_START,
  ZOOM_END,
  ZOOM_FROM,
  ZOOM_TO,
} from './constants';

/**
 * MoldCrossSection renders the mold shape:
 * - Outer shell (rectangle)
 * - Nozzle at the top (dimmed)
 * - Cavity interior (dimmed)
 * - Left and right walls (bright, glowing)
 *
 * The whole mold zooms from 1.0 to 1.15 in the first 30 frames.
 */
export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // Zoom animation
  const scale = interpolate(frame, [ZOOM_START, ZOOM_END], [ZOOM_FROM, ZOOM_TO], {
    easing: Easing.inOut(Easing.ease),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Walls brighten during zoom
  const wallBrightness = interpolate(frame, [0, 30], [0.3, 1.0], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Nozzle and cavity dim during zoom
  const dimFactor = interpolate(frame, [0, 30], [0.4, DIMMED_OPACITY], {
    easing: Easing.inOut(Easing.ease),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const cx = CANVAS_WIDTH / 2;
  const cy = CANVAS_HEIGHT / 2;

  // Outer shell rect
  const outerX = cx - MOLD_OUTER_WIDTH / 2;
  const outerY = cy - MOLD_OUTER_HEIGHT / 2;

  // Inner cavity rect
  const innerX = cx - MOLD_INNER_WIDTH / 2;
  const innerY = cy - MOLD_INNER_HEIGHT / 2;

  // Nozzle (top center, above outer shell)
  const nozzleX = cx - NOZZLE_WIDTH / 2;
  const nozzleY = outerY - NOZZLE_HEIGHT;

  // Wall segments: left wall and right wall of the mold
  const leftWallX = innerX;
  const rightWallX = innerX + MOLD_INNER_WIDTH;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
      }}
    >
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
      >
        <defs>
          <filter id="wallGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="6" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Outer shell */}
        <rect
          x={outerX}
          y={outerY}
          width={MOLD_OUTER_WIDTH}
          height={MOLD_OUTER_HEIGHT}
          fill="none"
          stroke={MOLD_STROKE_COLOR}
          strokeWidth={MOLD_STROKE_WIDTH}
          rx={4}
        />

        {/* Nozzle (dimmed) */}
        <g opacity={dimFactor}>
          <rect
            x={nozzleX}
            y={nozzleY}
            width={NOZZLE_WIDTH}
            height={NOZZLE_HEIGHT}
            fill="none"
            stroke={MOLD_STROKE_COLOR}
            strokeWidth={2}
            rx={2}
          />
          {/* Nozzle opening into mold */}
          <line
            x1={cx - 15}
            y1={outerY}
            x2={cx + 15}
            y2={outerY}
            stroke={WALL_COLOR}
            strokeWidth={2}
          />
        </g>

        {/* Cavity interior (dimmed) */}
        <rect
          x={innerX}
          y={innerY}
          width={MOLD_INNER_WIDTH}
          height={MOLD_INNER_HEIGHT}
          fill={WALL_COLOR}
          fillOpacity={dimFactor * 0.1}
          stroke={MOLD_STROKE_COLOR}
          strokeWidth={1}
          strokeOpacity={dimFactor}
          rx={2}
        />

        {/* Left wall — bright, with glow */}
        <line
          x1={leftWallX}
          y1={innerY}
          x2={leftWallX}
          y2={innerY + MOLD_INNER_HEIGHT}
          stroke={WALL_COLOR}
          strokeWidth={MOLD_STROKE_WIDTH}
          opacity={wallBrightness}
          filter="url(#wallGlow)"
        />

        {/* Right wall — bright, with glow */}
        <line
          x1={rightWallX}
          y1={innerY}
          x2={rightWallX}
          y2={innerY + MOLD_INNER_HEIGHT}
          stroke={WALL_COLOR}
          strokeWidth={MOLD_STROKE_WIDTH}
          opacity={wallBrightness}
          filter="url(#wallGlow)"
        />

        {/* Horizontal wall segments connecting left-right (top and bottom) */}
        <line
          x1={innerX}
          y1={innerY}
          x2={innerX + MOLD_INNER_WIDTH}
          y2={innerY}
          stroke={WALL_COLOR}
          strokeWidth={2}
          opacity={wallBrightness * 0.6}
        />
        <line
          x1={innerX}
          y1={innerY + MOLD_INNER_HEIGHT}
          x2={innerX + MOLD_INNER_WIDTH}
          y2={innerY + MOLD_INNER_HEIGHT}
          stroke={WALL_COLOR}
          strokeWidth={2}
          opacity={wallBrightness * 0.6}
        />
      </svg>
    </div>
  );
};
