import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TIMING, WALL_PULSE_TRIGGERS } from './constants';

/**
 * Simplified mold cross-section diagram rendered as background context.
 * Shows a rectangular mold cavity with thick walls that pulse amber on triggers.
 */
export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // Dim from full to 0.2 over first 30 frames
  const baseOpacity = interpolate(frame, [0, TIMING.moldDimEnd], [0.6, 0.2], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Calculate pulse glow from triggers
  let pulseGlow = 0;
  for (const trigger of WALL_PULSE_TRIGGERS) {
    if (frame >= trigger && frame < trigger + 20) {
      const localProgress = interpolate(
        frame,
        [trigger, trigger + 10, trigger + 20],
        [0, 1, 0],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      );
      pulseGlow = Math.max(pulseGlow, localProgress);
    }
  }

  // Intensified pulse during wall pulse phase (frames 330-390)
  if (frame >= TIMING.wallPulseStart && frame <= TIMING.wallPulseEnd) {
    const cycleLength = 20;
    const elapsed = frame - TIMING.wallPulseStart;
    const cyclePos = (elapsed % cycleLength) / cycleLength;
    const sinePulse = Math.sin(cyclePos * Math.PI);
    pulseGlow = Math.max(pulseGlow, sinePulse * 0.8);
  }

  const wallOpacity = interpolate(pulseGlow, [0, 1], [0.3, 0.7]);
  const finalWallOpacity = baseOpacity + pulseGlow * 0.5;
  const glowSpread = interpolate(pulseGlow, [0, 1], [0, 30]);

  const cx = 960;
  const cy = 500;
  const outerW = 500;
  const outerH = 300;
  const wallThickness = 40;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        opacity: baseOpacity,
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          <filter id="moldGlow">
            <feGaussianBlur
              stdDeviation={glowSpread}
              result="blur"
            />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Outer mold body */}
        <rect
          x={cx - outerW / 2}
          y={cy - outerH / 2}
          width={outerW}
          height={outerH}
          rx={12}
          fill={COLORS.moldWall}
          opacity={finalWallOpacity}
          filter="url(#moldGlow)"
        />

        {/* Inner cavity */}
        <rect
          x={cx - outerW / 2 + wallThickness}
          y={cy - outerH / 2 + wallThickness}
          width={outerW - wallThickness * 2}
          height={outerH - wallThickness * 2}
          rx={6}
          fill={COLORS.moldCavity}
          opacity={0.9}
        />

        {/* Top wall highlight */}
        <rect
          x={cx - outerW / 2 + 20}
          y={cy - outerH / 2 + 8}
          width={outerW - 40}
          height={4}
          rx={2}
          fill={COLORS.amber}
          opacity={wallOpacity * 0.6}
        />

        {/* Bottom wall highlight */}
        <rect
          x={cx - outerW / 2 + 20}
          y={cy + outerH / 2 - 12}
          width={outerW - 40}
          height={4}
          rx={2}
          fill={COLORS.amber}
          opacity={wallOpacity * 0.6}
        />

        {/* Left wall highlight */}
        <rect
          x={cx - outerW / 2 + 8}
          y={cy - outerH / 2 + 20}
          width={4}
          height={outerH - 40}
          rx={2}
          fill={COLORS.amber}
          opacity={wallOpacity * 0.6}
        />

        {/* Right wall highlight */}
        <rect
          x={cx + outerW / 2 - 12}
          y={cy - outerH / 2 + 20}
          width={4}
          height={outerH - 40}
          rx={2}
          fill={COLORS.amber}
          opacity={wallOpacity * 0.6}
        />

        {/* Label */}
        <text
          x={cx}
          y={cy + 5}
          textAnchor="middle"
          fill={COLORS.amber}
          opacity={wallOpacity * 0.4}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          letterSpacing={3}
        >
          MOLD
        </text>

        {/* Injection gate (top center) */}
        <path
          d={`M ${cx - 15} ${cy - outerH / 2} L ${cx} ${cy - outerH / 2 - 30} L ${cx + 15} ${cy - outerH / 2}`}
          fill="none"
          stroke={COLORS.amber}
          strokeWidth={2}
          opacity={wallOpacity * 0.5}
        />
      </svg>
    </div>
  );
};
