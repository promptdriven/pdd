import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import { BG_COLOR, TOTAL_FRAMES, WALL_COLOR } from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { MoldCrossSection } from './MoldCrossSection';
import { WallCounter } from './WallCounter';
import { TerminalScroll } from './TerminalScroll';

export const defaultPart3MoldParts06RatchetTimelapseProps = {};

export const Part3MoldParts06RatchetTimelapse: React.FC = () => {
  const frame = useCurrentFrame();

  // Subtle overall vignette that darkens edges
  const vignetteOpacity = interpolate(frame, [0, 30], [0.3, 0.5], {
    extrapolateRight: 'clamp',
  });

  // Title text fade-in at start
  const titleOpacity = interpolate(frame, [0, 20], [0, 0.85], {
    extrapolateRight: 'clamp',
  });

  // Title fades out once timelapse is rolling
  const titleFadeOut = interpolate(frame, [60, 90], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // "Ratchet" indicator bar grows over time
  const ratchetBarWidth = interpolate(frame, [0, TOTAL_FRAMES], [0, 300], {
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Mold cross-section with animated walls */}
      <MoldCrossSection />

      {/* Wall counter (top-right) */}
      <WallCounter />

      {/* Terminal with scrolling test output (bottom-right) */}
      <TerminalScroll />

      {/* Title overlay */}
      <div
        style={{
          position: 'absolute',
          left: 80,
          top: 50,
          opacity: titleOpacity * titleFadeOut,
        }}
      >
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 28,
            fontWeight: 700,
            color: '#FFFFFF',
            letterSpacing: '-0.02em',
          }}
        >
          The Ratchet Effect
        </div>
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 400,
            color: '#94A3B8',
            marginTop: 6,
          }}
        >
          Tests only accumulate. The mold only gets more precise.
        </div>
      </div>

      {/* Ratchet progress bar (bottom-left) */}
      <div
        style={{
          position: 'absolute',
          left: 80,
          bottom: 60,
          display: 'flex',
          flexDirection: 'column',
          gap: 6,
        }}
      >
        <div
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 10,
            color: '#64748B',
            letterSpacing: '0.1em',
            fontWeight: 600,
          }}
        >
          PRECISION
        </div>
        <div
          style={{
            width: 300,
            height: 4,
            backgroundColor: '#1E293B',
            borderRadius: 2,
            overflow: 'hidden',
          }}
        >
          <div
            style={{
              width: ratchetBarWidth,
              height: '100%',
              backgroundColor: WALL_COLOR,
              borderRadius: 2,
              boxShadow: `0 0 8px ${WALL_COLOR}66`,
            }}
          />
        </div>
      </div>

      {/* Vignette overlay */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          background:
            'radial-gradient(ellipse at center, transparent 50%, rgba(0,0,0,0.6) 100%)',
          opacity: vignetteOpacity,
          pointerEvents: 'none',
        }}
      />
    </AbsoluteFill>
  );
};

export default Part3MoldParts06RatchetTimelapse;
