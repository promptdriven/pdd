import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WALL_BLUE,
  TEXT_PRIMARY,
  NEW_WALL,
  WALL_SLIDE_START,
  WALL_SLIDE_DURATION,
  WALL_GLOW_START,
  WALL_LABEL_FADE_START,
  WALL_LABEL_FADE_DURATION,
} from './constants';

export const NewWall: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < WALL_SLIDE_START) return null;

  const localFrame = frame - WALL_SLIDE_START;

  // Slide-in with back easing (overshoot)
  // Easing.back(1.5) provides a slight overshoot
  const slideProgress = interpolate(
    localFrame,
    [0, WALL_SLIDE_DURATION],
    [0, 1],
    {
      easing: Easing.out(Easing.back(1.5)),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const translateX = interpolate(slideProgress, [0, 1], [250, 0]);

  // Glow pulse on arrival
  const glowOpacity = (() => {
    if (frame < WALL_GLOW_START) return 0;
    const glowLocal = frame - WALL_GLOW_START;
    if (glowLocal < 15) {
      return interpolate(glowLocal, [0, 8, 15], [0, 0.5, 0.15], {
        extrapolateRight: 'clamp',
      });
    }
    return interpolate(
      glowLocal,
      [15, 60],
      [0.15, 0.08],
      { extrapolateRight: 'clamp' }
    );
  })();

  // Label fade-in
  const labelOpacity = interpolate(
    frame,
    [WALL_LABEL_FADE_START, WALL_LABEL_FADE_START + WALL_LABEL_FADE_DURATION],
    [0, 0.85],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <>
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          <filter id="newWallGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="15" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Glow behind wall */}
        <rect
          x={NEW_WALL.x - 10}
          y={NEW_WALL.y - 10}
          width={NEW_WALL.width + 20}
          height={NEW_WALL.height + 20}
          fill={WALL_BLUE}
          opacity={glowOpacity}
          filter="url(#newWallGlow)"
          transform={`translate(${translateX}, 0)`}
        />

        {/* Wall rectangle */}
        <rect
          x={NEW_WALL.x}
          y={NEW_WALL.y}
          width={NEW_WALL.width}
          height={NEW_WALL.height}
          fill={WALL_BLUE}
          opacity={0.85}
          transform={`translate(${translateX}, 0)`}
        />
      </svg>

      {/* Label */}
      {labelOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            left: NEW_WALL.x + NEW_WALL.width / 2 + translateX - 75,
            top: NEW_WALL.y - 30,
            opacity: labelOpacity,
            display: 'flex',
            justifyContent: 'center',
          }}
        >
          <span
            style={{
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 14,
              color: TEXT_PRIMARY,
              backgroundColor: `rgba(74, 144, 217, 0.15)`,
              padding: '3px 10px',
              borderRadius: 10,
              whiteSpace: 'nowrap',
            }}
          >
            {NEW_WALL.label}
          </span>
        </div>
      )}
    </>
  );
};
