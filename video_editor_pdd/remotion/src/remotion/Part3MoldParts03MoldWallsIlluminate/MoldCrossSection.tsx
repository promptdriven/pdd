import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MOLD_X,
  MOLD_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_WALL_THICKNESS,
  MOLD_OUTER_STROKE,
  MOLD_OUTER_STROKE_WIDTH,
  WALL_COLOR,
  DIMMED_OPACITY,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  ZOOM_START,
  ZOOM_END,
  ZOOM_FROM,
  ZOOM_TO,
  WALL_SEGMENT_POSITIONS,
  WALL_DATA,
  WALL_GLOW_MIN,
  WALL_GLOW_MAX,
  WALL_GLOW_DURATION,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from './constants';

export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // Zoom animation
  const scale = interpolate(frame, [ZOOM_START, ZOOM_END], [ZOOM_FROM, ZOOM_TO], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  // Nozzle/cavity dim during transition (frames 0-30)
  const dimProgress = interpolate(frame, [0, 30], [0.3, DIMMED_OPACITY], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Walls brighten during transition (frames 0-30)
  const wallBrightness = interpolate(frame, [0, 30], [0.3, 1.0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const centerX = CANVAS_WIDTH / 2;
  const centerY = CANVAS_HEIGHT / 2;

  // Nozzle position (top center of mold)
  const nozzleX = MOLD_X + (MOLD_WIDTH - NOZZLE_WIDTH) / 2;
  const nozzleY = MOLD_Y - NOZZLE_HEIGHT;

  // Cavity interior
  const cavityX = MOLD_X + MOLD_WALL_THICKNESS;
  const cavityY = MOLD_Y + MOLD_WALL_THICKNESS;
  const cavityW = MOLD_WIDTH - 2 * MOLD_WALL_THICKNESS;
  const cavityH = MOLD_HEIGHT - 2 * MOLD_WALL_THICKNESS;

  return (
    <div
      style={{
        position: 'absolute',
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        transform: `scale(${scale})`,
        transformOrigin: `${centerX}px ${centerY}px`,
      }}
    >
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          <filter id="wallGlow">
            <feGaussianBlur stdDeviation="6" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
          <filter id="segmentGlow">
            <feGaussianBlur stdDeviation="8" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Nozzle (dimmed) */}
        <rect
          x={nozzleX}
          y={nozzleY}
          width={NOZZLE_WIDTH}
          height={NOZZLE_HEIGHT}
          fill="none"
          stroke={MOLD_OUTER_STROKE}
          strokeWidth={MOLD_OUTER_STROKE_WIDTH}
          opacity={dimProgress}
        />
        {/* Nozzle channel */}
        <rect
          x={nozzleX + 20}
          y={nozzleY}
          width={NOZZLE_WIDTH - 40}
          height={NOZZLE_HEIGHT + 10}
          fill={WALL_COLOR}
          opacity={dimProgress * 0.3}
        />

        {/* Outer mold shell */}
        <rect
          x={MOLD_X}
          y={MOLD_Y}
          width={MOLD_WIDTH}
          height={MOLD_HEIGHT}
          fill="none"
          stroke={MOLD_OUTER_STROKE}
          strokeWidth={MOLD_OUTER_STROKE_WIDTH}
          rx={4}
        />

        {/* Left wall (full) */}
        <rect
          x={MOLD_X}
          y={MOLD_Y}
          width={MOLD_WALL_THICKNESS}
          height={MOLD_HEIGHT}
          fill={WALL_COLOR}
          opacity={wallBrightness * 0.25}
          filter="url(#wallGlow)"
          rx={2}
        />

        {/* Right wall (full) */}
        <rect
          x={MOLD_X + MOLD_WIDTH - MOLD_WALL_THICKNESS}
          y={MOLD_Y}
          width={MOLD_WALL_THICKNESS}
          height={MOLD_HEIGHT}
          fill={WALL_COLOR}
          opacity={wallBrightness * 0.25}
          filter="url(#wallGlow)"
          rx={2}
        />

        {/* Bottom wall */}
        <rect
          x={MOLD_X}
          y={MOLD_Y + MOLD_HEIGHT - MOLD_WALL_THICKNESS}
          width={MOLD_WIDTH}
          height={MOLD_WALL_THICKNESS}
          fill={WALL_COLOR}
          opacity={wallBrightness * 0.2}
          filter="url(#wallGlow)"
          rx={2}
        />

        {/* Top wall */}
        <rect
          x={MOLD_X}
          y={MOLD_Y}
          width={MOLD_WIDTH}
          height={MOLD_WALL_THICKNESS}
          fill={WALL_COLOR}
          opacity={wallBrightness * 0.2}
          filter="url(#wallGlow)"
          rx={2}
        />

        {/* Cavity interior (dimmed) */}
        <rect
          x={cavityX}
          y={cavityY}
          width={cavityW}
          height={cavityH}
          fill={WALL_COLOR}
          opacity={dimProgress * 0.08}
          rx={2}
        />

        {/* Illuminated wall segments */}
        {WALL_DATA.map((wall, index) => {
          const seg = WALL_SEGMENT_POSITIONS[index];
          const segFrame = frame - wall.frameIn;

          const glowOpacity =
            segFrame < 0
              ? WALL_GLOW_MIN
              : interpolate(
                  segFrame,
                  [0, WALL_GLOW_DURATION],
                  [WALL_GLOW_MIN, WALL_GLOW_MAX],
                  {
                    extrapolateLeft: 'clamp',
                    extrapolateRight: 'clamp',
                    easing: Easing.out(Easing.quad),
                  }
                );

          return (
            <rect
              key={`wall-seg-${index}`}
              x={seg.x}
              y={seg.y}
              width={seg.width}
              height={seg.height}
              fill={WALL_COLOR}
              opacity={glowOpacity}
              filter="url(#segmentGlow)"
              rx={2}
            />
          );
        })}

        {/* Decorative inner wall ridges */}
        {[200, 320, 440, 560, 680].map((yOff) => (
          <React.Fragment key={`ridge-${yOff}`}>
            <line
              x1={MOLD_X + MOLD_WALL_THICKNESS}
              y1={MOLD_Y + yOff}
              x2={MOLD_X + MOLD_WALL_THICKNESS + 15}
              y2={MOLD_Y + yOff}
              stroke={WALL_COLOR}
              strokeWidth={1}
              opacity={wallBrightness * 0.15}
            />
            <line
              x1={MOLD_X + MOLD_WIDTH - MOLD_WALL_THICKNESS}
              y1={MOLD_Y + yOff}
              x2={MOLD_X + MOLD_WIDTH - MOLD_WALL_THICKNESS - 15}
              y2={MOLD_Y + yOff}
              stroke={WALL_COLOR}
              strokeWidth={1}
              opacity={wallBrightness * 0.15}
            />
          </React.Fragment>
        ))}
      </svg>
    </div>
  );
};
