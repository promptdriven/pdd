import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { MOLD, WALL_PULSE_TRIGGERS, TIMING, COLORS } from './constants';

/**
 * Dimmed mold cross-section background diagram.
 * Shows an outer mold shell with inner cavity and glowing amber walls.
 * Walls pulse at specific trigger frames.
 */
export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // Dim from full to 0.2 opacity over first 30 frames
  const baseOpacity = interpolate(frame, [0, TIMING.moldDimEnd], [0.6, 0.2], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Calculate wall pulse glow
  let pulseGlow = 0;
  for (const trigger of WALL_PULSE_TRIGGERS) {
    if (frame >= trigger && frame < trigger + 20) {
      const localFrame = frame - trigger;
      const pulse = interpolate(localFrame, [0, 10, 20], [0, 1, 0], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      });
      pulseGlow = Math.max(pulseGlow, pulse);
    }
  }

  // Phase 5: sustained wall pulse brightness
  if (frame >= TIMING.wallPulseStart && frame < TIMING.wallPulseStart + TIMING.wallPulseDur) {
    const localFrame = frame - TIMING.wallPulseStart;
    const sustained = interpolate(localFrame, [0, 20, 40, 60], [0, 1, 0.8, 0.6], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });
    pulseGlow = Math.max(pulseGlow, sustained);
  }

  const wallOpacity = interpolate(pulseGlow, [0, 1], [0.3, 0.7]);
  const combinedOpacity = Math.min(1, baseOpacity + pulseGlow * 0.3);

  const cx = MOLD.centerX;
  const cy = MOLD.centerY;
  const ow = MOLD.outerWidth;
  const oh = MOLD.outerHeight;
  const wt = MOLD.wallThickness;
  const iw = MOLD.innerWidth;
  const ih = MOLD.innerHeight;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        opacity: combinedOpacity,
      }}
    >
      <svg width={1920} height={1080} viewBox="0 0 1920 1080">
        {/* Outer mold shell */}
        <rect
          x={cx - ow / 2}
          y={cy - oh / 2}
          width={ow}
          height={oh}
          rx={12}
          ry={12}
          fill="none"
          stroke={COLORS.amber}
          strokeWidth={3}
          opacity={0.4}
        />

        {/* Left wall */}
        <rect
          x={cx - ow / 2 + 15}
          y={cy - ih / 2}
          width={wt}
          height={ih}
          rx={4}
          fill={COLORS.amber}
          opacity={wallOpacity}
        />

        {/* Right wall */}
        <rect
          x={cx + ow / 2 - 15 - wt}
          y={cy - ih / 2}
          width={wt}
          height={ih}
          rx={4}
          fill={COLORS.amber}
          opacity={wallOpacity}
        />

        {/* Top wall */}
        <rect
          x={cx - iw / 2}
          y={cy - oh / 2 + 15}
          width={iw}
          height={wt}
          rx={4}
          fill={COLORS.amber}
          opacity={wallOpacity}
        />

        {/* Bottom wall */}
        <rect
          x={cx - iw / 2}
          y={cy + oh / 2 - 15 - wt}
          width={iw}
          height={wt}
          rx={4}
          fill={COLORS.amber}
          opacity={wallOpacity}
        />

        {/* Inner cavity */}
        <rect
          x={cx - iw / 2 + wt}
          y={cy - ih / 2 + wt}
          width={iw - 2 * wt}
          height={ih - 2 * wt}
          rx={6}
          fill={COLORS.amber}
          opacity={0.05}
        />

        {/* Wall glow effect */}
        {pulseGlow > 0 && (
          <>
            <rect
              x={cx - ow / 2}
              y={cy - oh / 2}
              width={ow}
              height={oh}
              rx={12}
              fill="none"
              stroke={COLORS.amber}
              strokeWidth={6}
              opacity={pulseGlow * 0.3}
              filter="url(#moldGlow)"
            />
            <defs>
              <filter id="moldGlow" x="-20%" y="-20%" width="140%" height="140%">
                <feGaussianBlur stdDeviation="8" result="blur" />
                <feMerge>
                  <feMergeNode in="blur" />
                  <feMergeNode in="SourceGraphic" />
                </feMerge>
              </filter>
            </defs>
          </>
        )}

        {/* Label */}
        <text
          x={cx}
          y={cy + oh / 2 + 35}
          textAnchor="middle"
          fontFamily="Inter, system-ui, sans-serif"
          fontSize={12}
          fontWeight={500}
          fill={COLORS.amber}
          opacity={0.3}
        >
          MOLD WALLS
        </text>
      </svg>
    </div>
  );
};
