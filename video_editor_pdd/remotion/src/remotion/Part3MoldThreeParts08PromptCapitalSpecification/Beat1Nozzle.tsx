import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { NOZZLE_BLUE, MUTED_GRAY, PROMPT_TEXT } from './constants';

/**
 * Beat 1 — Nozzle Labels (frames 0-150)
 * Mold diagram with nozzle highlighted, text flowing into it.
 */

// ── Mold cross-section (simplified) ──
const MoldCrossSection: React.FC<{ nozzleOpacity: number }> = ({ nozzleOpacity }) => {
  return (
    <svg
      width={500}
      height={400}
      viewBox="0 0 500 400"
      style={{ position: 'absolute', left: 710, top: 300 }}
    >
      {/* Outer mold shell — dimmed */}
      <rect
        x={50}
        y={120}
        width={400}
        height={230}
        rx={16}
        fill="none"
        stroke="#334155"
        strokeWidth={2}
        opacity={0.15}
      />
      {/* Inner cavity — dimmed */}
      <rect
        x={100}
        y={170}
        width={300}
        height={130}
        rx={10}
        fill="#1E293B"
        opacity={0.15}
        stroke="#475569"
        strokeWidth={1}
      />
      {/* Ejector pins — dimmed */}
      {[160, 250, 340].map((cx) => (
        <rect
          key={cx}
          x={cx - 4}
          y={300}
          width={8}
          height={40}
          rx={2}
          fill="#475569"
          opacity={0.12}
        />
      ))}

      {/* Nozzle — highlighted */}
      <g opacity={nozzleOpacity}>
        {/* Nozzle glow */}
        <ellipse
          cx={250}
          cy={120}
          rx={50}
          ry={30}
          fill={NOZZLE_BLUE}
          opacity={0.12}
          filter="url(#nozzleGlow)"
        />
        {/* Nozzle body */}
        <path
          d="M 220 40 L 220 120 Q 220 130 230 130 L 270 130 Q 280 130 280 120 L 280 40 Z"
          fill="none"
          stroke={NOZZLE_BLUE}
          strokeWidth={3}
          opacity={0.6}
        />
        {/* Nozzle tip / opening */}
        <path
          d="M 235 130 L 235 145 Q 235 155 245 155 L 255 155 Q 265 155 265 145 L 265 130"
          fill="none"
          stroke={NOZZLE_BLUE}
          strokeWidth={2}
          opacity={0.5}
        />
        {/* Runner channel into cavity */}
        <line
          x1={250}
          y1={155}
          x2={250}
          y2={170}
          stroke={NOZZLE_BLUE}
          strokeWidth={2}
          opacity={0.4}
        />
      </g>

      <defs>
        <filter id="nozzleGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="12" />
        </filter>
      </defs>
    </svg>
  );
};

// ── Flowing text particles ──
const FlowingText: React.FC<{ frame: number }> = ({ frame }) => {
  const words = PROMPT_TEXT.split(' ');
  const startFrame = 30;
  const adjustedFrame = frame - startFrame;
  if (adjustedFrame < 0) return null;

  return (
    <>
      {words.map((word, i) => {
        const wordDelay = i * 6;
        const wordFrame = adjustedFrame - wordDelay;
        if (wordFrame < 0) return null;

        // Each word flows downward toward the nozzle
        const targetY = 420; // nozzle entry point (relative to page)
        const startY = 280 + i * 2;
        const progress = interpolate(wordFrame, [0, 50], [0, 1], {
          extrapolateRight: 'clamp',
        });

        const y = interpolate(progress, [0, 1], [startY, targetY]);
        // Horizontal wobble
        const wobbleX =
          Math.sin(wordFrame * 0.15 + i * 1.2) * 8 * (1 - progress);
        const x = 960 + wobbleX + (i % 3 === 0 ? -30 : i % 3 === 1 ? 0 : 30);

        const opacity = interpolate(
          progress,
          [0, 0.1, 0.85, 1],
          [0, 0.7, 0.7, 0],
          { extrapolateRight: 'clamp' }
        );

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: x,
              top: y,
              transform: 'translateX(-50%)',
              fontFamily: 'JetBrains Mono, monospace',
              fontSize: 11,
              color: NOZZLE_BLUE,
              opacity,
              whiteSpace: 'nowrap',
              pointerEvents: 'none',
            }}
          >
            {word}
          </div>
        );
      })}
    </>
  );
};

// ── File label ──
const FileLabel: React.FC<{ opacity: number }> = ({ opacity }) => (
  <div
    style={{
      position: 'absolute',
      left: 960,
      top: 365,
      transform: 'translateX(-50%)',
      fontFamily: 'JetBrains Mono, monospace',
      fontSize: 10,
      color: MUTED_GRAY,
      opacity: opacity * 0.5,
      whiteSpace: 'nowrap',
    }}
  >
    user_parser.prompt
  </div>
);

// ── Nozzle labels (intent / requirements / constraints) ──
const NozzleLabels: React.FC<{ frame: number }> = ({ frame }) => {
  const labels = ['intent', 'requirements', 'constraints'];
  const startFrame = 90;

  return (
    <>
      {labels.map((label, i) => {
        const delay = startFrame + i * 10;
        const localFrame = frame - delay;
        if (localFrame < 0) return null;

        const opacity = interpolate(localFrame, [0, 15, 45, 60], [0, 0.5, 0.5, 0], {
          extrapolateRight: 'clamp',
        });

        const xOffset = (i - 1) * 120;

        return (
          <div
            key={label}
            style={{
              position: 'absolute',
              left: 960 + xOffset,
              top: 740,
              transform: 'translateX(-50%)',
              fontFamily: 'Inter, sans-serif',
              fontSize: 12,
              color: NOZZLE_BLUE,
              opacity,
              letterSpacing: 1,
              textTransform: 'uppercase',
            }}
          >
            {label}
          </div>
        );
      })}
    </>
  );
};

export const Beat1Nozzle: React.FC = () => {
  const frame = useCurrentFrame();

  // Nozzle illumination: easeOut(quad) over first 20 frames
  const nozzleOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Overall mold fade-in
  const moldFade = interpolate(frame, [0, 25], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // File label fade
  const fileLabelOpacity = interpolate(frame, [30, 50], [0, 1], {
    extrapolateRight: 'clamp',
  });

  // Nozzle pulse (frames 90-150)
  const pulsePhase = frame > 90 ? Math.sin((frame - 90) * 0.12) * 0.15 : 0;

  return (
    <AbsoluteFill style={{ opacity: moldFade }}>
      <MoldCrossSection nozzleOpacity={nozzleOpacity + pulsePhase} />
      <FlowingText frame={frame} />
      <FileLabel opacity={fileLabelOpacity} />
      <NozzleLabels frame={frame} />
    </AbsoluteFill>
  );
};
