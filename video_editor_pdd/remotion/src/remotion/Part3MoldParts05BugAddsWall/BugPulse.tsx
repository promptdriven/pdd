import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BUG_RED,
  BUG_X,
  BUG_Y,
  BUG_DISCOVER_START,
  BUG_HOLD_END,
} from './constants';

const RING_COUNT = 3;
const RING_DELAY = 5; // frames between each ring
const RING_DURATION = 15;
const MAX_RADIUS = 80;

export const BugPulse: React.FC = () => {
  const frame = useCurrentFrame();

  // "BUG" text fades in at frame 10, fades out at frame 60-75
  const bugTextOpacity = interpolate(
    frame,
    [10, 25, BUG_HOLD_END, BUG_HOLD_END + 15],
    [0, 1, 1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <>
      {/* Concentric pulse rings */}
      {Array.from({ length: RING_COUNT }).map((_, i) => {
        const ringStart = BUG_DISCOVER_START + i * RING_DELAY;
        const ringEnd = ringStart + RING_DURATION;

        const progress = interpolate(
          frame,
          [ringStart, ringEnd],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
        );

        const radius = 20 + progress * MAX_RADIUS;
        const opacity = interpolate(progress, [0, 0.3, 1], [0, 0.6, 0]);

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: BUG_X - radius,
              top: BUG_Y - radius,
              width: radius * 2,
              height: radius * 2,
              borderRadius: '50%',
              background: `radial-gradient(circle, ${BUG_RED}${Math.round(opacity * 255).toString(16).padStart(2, '0')} 0%, transparent 70%)`,
              pointerEvents: 'none',
            }}
          />
        );
      })}

      {/* Persistent glow while bug is visible */}
      {frame < BUG_HOLD_END + 15 && (
        <div
          style={{
            position: 'absolute',
            left: BUG_X - 40,
            top: BUG_Y - 40,
            width: 80,
            height: 80,
            borderRadius: '50%',
            background: `radial-gradient(circle, ${BUG_RED}40 0%, transparent 70%)`,
            opacity: interpolate(
              frame,
              [0, 15, BUG_HOLD_END, BUG_HOLD_END + 15],
              [0, 0.8, 0.8, 0],
              { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
            ),
          }}
        />
      )}

      {/* "BUG" text */}
      <div
        style={{
          position: 'absolute',
          left: BUG_X - 40,
          top: BUG_Y - 55,
          width: 80,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 28,
          fontWeight: 700,
          color: BUG_RED,
          opacity: bugTextOpacity,
          textShadow: `0 0 20px ${BUG_RED}80`,
          letterSpacing: 4,
        }}
      >
        BUG
      </div>
    </>
  );
};
