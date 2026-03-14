import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION, WAVEFORM, type WaveOverlayLayout } from './constants';

/**
 * Generates an SVG path for a sine wave within the waveform chart area.
 * Uses the amplitude/frequency from the spec's structured data.
 */
const buildSinePath = (layout: WaveOverlayLayout): string => {
  const chartW = layout.waveform.right - layout.waveform.left;
  const chartH = layout.waveform.bottom - layout.waveform.top;
  const midY = layout.waveform.top + chartH / 2;

  const points: string[] = [];
  for (let i = 0; i <= WAVEFORM.samples; i++) {
    const t = i / WAVEFORM.samples;
    const x = layout.waveform.left + t * chartW;
    // sine wave: amplitude * sin(2π * frequency * t * xRange)
    const yNorm = WAVEFORM.amplitude * Math.sin(2 * Math.PI * WAVEFORM.frequency * t * 3);
    // Map normalized [-1,1] range to pixel space (inverted Y)
    const y = midY - yNorm * (chartH / 2);
    points.push(`${i === 0 ? 'M' : 'L'} ${x.toFixed(2)} ${y.toFixed(2)}`);
  }

  return points.join(' ');
};

/**
 * Builds a closed path for the gradient fill beneath the sine curve.
 */
const buildFillPath = (layout: WaveOverlayLayout): string => {
  const sinePath = buildSinePath(layout);
  const lastX = layout.waveform.right;
  const firstX = layout.waveform.left;
  const bottomY = layout.waveform.bottom;

  return `${sinePath} L ${lastX.toFixed(2)} ${bottomY.toFixed(2)} L ${firstX.toFixed(2)} ${bottomY.toFixed(2)} Z`;
};

interface WaveformGraphProps {
  layout: WaveOverlayLayout;
}

export const WaveformGraph: React.FC<WaveformGraphProps> = ({ layout }) => {
  const frame = useCurrentFrame();

  // Linear draw progress from frame 8 to 22
  const drawProgress = interpolate(
    frame,
    [ANIMATION.waveDrawStart, ANIMATION.waveDrawEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const sinePath = buildSinePath(layout);
  const fillPath = buildFillPath(layout);

  // strokeDashoffset for progressive draw
  const pathLength = 3000;
  const dashOffset = pathLength * (1 - drawProgress);

  // Clip fill region to drawn portion
  const revealWidth = (layout.waveform.right - layout.waveform.left) * drawProgress;

  return (
    <svg
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: layout.width,
        height: layout.height,
        pointerEvents: 'none',
      }}
    >
      <defs>
        {/* Gradient fill beneath curve */}
        <linearGradient id="waveGradientFill" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={COLORS.waveStroke} stopOpacity={0.2} />
          <stop offset="100%" stopColor={COLORS.waveStroke} stopOpacity={0} />
        </linearGradient>
        {/* Clip to revealed portion */}
        <clipPath id="waveRevealClip04">
          <rect
            x={layout.waveform.left}
            y={0}
            width={revealWidth}
            height={layout.height}
          />
        </clipPath>
        {/* Soft glow filter */}
        <filter id="waveGlow04" x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur in="SourceGraphic" stdDeviation={WAVEFORM.glowBlur} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Fill beneath the wave */}
      <path
        d={fillPath}
        fill="url(#waveGradientFill)"
        clipPath="url(#waveRevealClip04)"
      />

      {/* Glow layer (behind the main stroke) */}
      <path
        d={sinePath}
        fill="none"
        stroke={COLORS.waveGlow}
        strokeWidth={WAVEFORM.strokeWidth + 6}
        strokeDasharray={pathLength}
        strokeDashoffset={dashOffset}
        strokeLinecap="round"
        filter="url(#waveGlow04)"
      />

      {/* Main waveform stroke */}
      <path
        d={sinePath}
        fill="none"
        stroke={COLORS.waveStroke}
        strokeWidth={WAVEFORM.strokeWidth}
        strokeDasharray={pathLength}
        strokeDashoffset={dashOffset}
        strokeLinecap="round"
      />
    </svg>
  );
};
