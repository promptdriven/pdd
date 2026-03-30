// Part1Economics07ContextWindowShrink.tsx
// Main component: Context Window Shrink — Codebase Growth vs. Fixed Window
// Duration: 1560 frames @ 30fps (~52s)
//
// Visualizes how a fixed-size AI context window becomes increasingly inadequate
// as a codebase grows from 4×4 → 8×8 → 16×16 → 32×32 blocks.

import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { BACKGROUND_COLOR, MISMATCH_START_FRAME } from './constants';
import { CodeBlockGrid } from './CodeBlockGrid';
import { ContextWindow } from './ContextWindow';
import { CoverageCounter } from './CoverageCounter';
import { MismatchHighlights } from './MismatchHighlights';

export const defaultPart1Economics07ContextWindowShrinkProps = {};

export const Part1Economics07ContextWindowShrink: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Title label — top-left */}
      <TitleLabel />

      {/* Growing code grid — uses global frame via useCurrentFrame */}
      <CodeBlockGrid />

      {/* Fixed-size context window overlay */}
      <ContextWindow />

      {/* Coverage counter (top-right) */}
      <CoverageCounter />

      {/* Mismatch highlights — Phase 3 (uses global frame internally) */}
      <MismatchHighlights />

      {/* Legend for red/green highlights */}
      <MismatchLegend />
    </AbsoluteFill>
  );
};

/** Small title in the top-left corner */
const TitleLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, 30], [0.85, 0.85], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: 60,
        top: 48,
        zIndex: 20,
        opacity,
      }}
    >
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 20,
          fontWeight: 600,
          color: '#E2E8F0',
          letterSpacing: '-0.01em',
        }}
      >
        Codebase Growth vs. Fixed Context Window
      </div>
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 400,
          color: '#94A3B8',
          opacity: 0.82,
          marginTop: 4,
        }}
      >
        The AI can only see what fits in its context window
      </div>
    </div>
  );
};

/** Legend that appears during the mismatch phase */
const MismatchLegend: React.FC = () => {
  const frame = useCurrentFrame();

  // Don't render before mismatch phase
  if (frame < MISMATCH_START_FRAME) return null;

  const opacity = interpolate(
    frame,
    [MISMATCH_START_FRAME, MISMATCH_START_FRAME + 30],
    [0, 0.9],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 60,
        bottom: 80,
        display: 'flex',
        flexDirection: 'column',
        gap: 10,
        opacity,
        zIndex: 20,
      }}
    >
      <div style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
        <div
          style={{
            width: 14,
            height: 14,
            borderRadius: 2,
            backgroundColor: '#EF4444',
            opacity: 0.5,
          }}
        />
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 13,
            color: '#EF4444',
            opacity: 0.78,
          }}
        >
          Irrelevant code grabbed by AI
        </span>
      </div>
      <div style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
        <div
          style={{
            width: 14,
            height: 14,
            borderRadius: 2,
            backgroundColor: '#5AAA6E',
            opacity: 0.5,
          }}
        />
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 13,
            color: '#5AAA6E',
            opacity: 0.78,
          }}
        >
          Needed code outside the window
        </span>
      </div>
    </div>
  );
};

export default Part1Economics07ContextWindowShrink;
