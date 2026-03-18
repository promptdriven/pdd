import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { COLORS, PROMPT_TEXT, PROMPT_FILE } from './constants';

/**
 * Beat 1 — Nozzle Labels (frames 0-150)
 * Mold diagram with nozzle illuminating blue.
 * Text flows into nozzle like liquid injection.
 */

const MOLD_CENTER_X = 960;
const MOLD_CENTER_Y = 500;

// Break prompt text into individual words for flowing animation
const PROMPT_WORDS = PROMPT_TEXT.split(' ');

const MoldDiagram: React.FC<{ nozzleOpacity: number }> = ({
  nozzleOpacity,
}) => {
  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Mold body (dimmed) */}
      {/* Left mold half */}
      <rect
        x={MOLD_CENTER_X - 200}
        y={MOLD_CENTER_Y - 80}
        width={180}
        height={250}
        rx={8}
        fill={COLORS.codePanel}
        opacity={0.15}
        stroke={COLORS.codeBorder}
        strokeWidth={1}
      />
      {/* Right mold half */}
      <rect
        x={MOLD_CENTER_X + 20}
        y={MOLD_CENTER_Y - 80}
        width={180}
        height={250}
        rx={8}
        fill={COLORS.codePanel}
        opacity={0.15}
        stroke={COLORS.codeBorder}
        strokeWidth={1}
      />
      {/* Cavity (center gap) */}
      <rect
        x={MOLD_CENTER_X - 15}
        y={MOLD_CENTER_Y - 40}
        width={30}
        height={200}
        rx={4}
        fill={COLORS.background}
        opacity={0.3}
        stroke={COLORS.codeBorder}
        strokeWidth={1}
      />
      {/* Nozzle (top, highlighted) */}
      <g>
        {/* Nozzle glow */}
        <ellipse
          cx={MOLD_CENTER_X}
          cy={MOLD_CENTER_Y - 100}
          rx={60}
          ry={35}
          fill={COLORS.nozzleBlue}
          opacity={nozzleOpacity * 0.2}
          filter="url(#nozzleGlow)"
        />
        {/* Nozzle body */}
        <path
          d={`M ${MOLD_CENTER_X - 40} ${MOLD_CENTER_Y - 130}
              L ${MOLD_CENTER_X - 15} ${MOLD_CENTER_Y - 80}
              L ${MOLD_CENTER_X + 15} ${MOLD_CENTER_Y - 80}
              L ${MOLD_CENTER_X + 40} ${MOLD_CENTER_Y - 130}
              Z`}
          fill={COLORS.nozzleBlue}
          opacity={nozzleOpacity * 0.6}
          stroke={COLORS.nozzleBlue}
          strokeWidth={3}
        />
        {/* Nozzle opening */}
        <rect
          x={MOLD_CENTER_X - 15}
          y={MOLD_CENTER_Y - 85}
          width={30}
          height={10}
          rx={2}
          fill={COLORS.nozzleBlue}
          opacity={nozzleOpacity * 0.8}
        />
      </g>

      {/* Runners (dimmed) */}
      <line
        x1={MOLD_CENTER_X}
        y1={MOLD_CENTER_Y - 40}
        x2={MOLD_CENTER_X - 100}
        y2={MOLD_CENTER_Y + 60}
        stroke={COLORS.codeBorder}
        strokeWidth={2}
        opacity={0.15}
      />
      <line
        x1={MOLD_CENTER_X}
        y1={MOLD_CENTER_Y - 40}
        x2={MOLD_CENTER_X + 100}
        y2={MOLD_CENTER_Y + 60}
        stroke={COLORS.codeBorder}
        strokeWidth={2}
        opacity={0.15}
      />

      {/* SVG filters */}
      <defs>
        <filter id="nozzleGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="12" />
        </filter>
      </defs>
    </svg>
  );
};

const FlowingTextParticle: React.FC<{
  word: string;
  index: number;
  totalWords: number;
  frame: number;
  startFrame: number;
}> = ({ word, index, totalWords, frame, startFrame }) => {
  const wordDelay = startFrame + index * 4; // stagger each word by 4 frames
  const elapsed = frame - wordDelay;

  if (elapsed < 0) return null;

  // Each word flows from above (y: 100) down toward nozzle (y: ~370)
  const targetY = MOLD_CENTER_Y - 130;
  const startY = 60;
  const travelFrames = 50;

  const progress = Math.min(elapsed / travelFrames, 1);

  const y = interpolate(progress, [0, 1], [startY, targetY], {
    easing: Easing.out(Easing.quad),
  });

  // Horizontal wobble using sine
  const wobbleX =
    Math.sin(elapsed * 0.15 + index * 1.2) * 8 * (1 - progress);

  // Words spread across a horizontal band
  const spreadX =
    MOLD_CENTER_X -
    120 +
    (index % 5) * 55 +
    wobbleX;

  // Fade in quickly, then settle
  const opacity = interpolate(progress, [0, 0.1, 0.8, 1], [0, 0.7, 0.7, 0.5]);

  // Scale down slightly as it settles
  const scale = interpolate(progress, [0, 1], [1.1, 0.9]);

  // Once settled, disappear into the nozzle
  const settledOpacity =
    elapsed > travelFrames + 20
      ? interpolate(
          elapsed - travelFrames - 20,
          [0, 15],
          [0.5, 0],
          { extrapolateRight: 'clamp' }
        )
      : opacity;

  return (
    <div
      style={{
        position: 'absolute',
        left: spreadX,
        top: y,
        fontFamily: 'JetBrains Mono, monospace',
        fontSize: 11,
        color: COLORS.nozzleBlue,
        opacity: settledOpacity,
        transform: `scale(${scale})`,
        whiteSpace: 'nowrap',
        pointerEvents: 'none',
      }}
    >
      {word}
    </div>
  );
};

export const Beat1Nozzle: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 0-30: Mold fades in, nozzle illuminates
  const nozzleOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Overall mold fade-in
  const moldOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateRight: 'clamp',
  });

  // File label appears at frame 30
  const fileLabelOpacity = interpolate(frame, [30, 50], [0, 0.5], {
    extrapolateRight: 'clamp',
  });

  // Nozzle pulse at frames 90-150
  const pulsePhase = frame > 90 ? (frame - 90) / 40 : 0;
  const pulse =
    frame > 90
      ? 0.85 + 0.15 * Math.sin(pulsePhase * Math.PI * 2)
      : 1;

  // Labels that briefly appear at frames 100-140
  const labelsOpacity = interpolate(frame, [100, 110, 130, 140], [0, 0.5, 0.5, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill style={{ opacity: moldOpacity }}>
      <MoldDiagram nozzleOpacity={nozzleOpacity * pulse} />

      {/* Flowing text particles (frames 30-90) */}
      {PROMPT_WORDS.map((word, i) => (
        <FlowingTextParticle
          key={i}
          word={word}
          index={i}
          totalWords={PROMPT_WORDS.length}
          frame={frame}
          startFrame={30}
        />
      ))}

      {/* File label */}
      <div
        style={{
          position: 'absolute',
          left: MOLD_CENTER_X - 70,
          top: MOLD_CENTER_Y - 180,
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 10,
          color: COLORS.labelMuted,
          opacity: fileLabelOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        {PROMPT_FILE}
      </div>

      {/* Brief labels: intent, requirements, constraints */}
      {['intent', 'requirements', 'constraints'].map((label, i) => (
        <div
          key={label}
          style={{
            position: 'absolute',
            left: MOLD_CENTER_X - 180 + i * 140,
            top: MOLD_CENTER_Y - 210,
            fontFamily: 'Inter, sans-serif',
            fontSize: 11,
            color: COLORS.nozzleBlue,
            opacity: labelsOpacity,
            textTransform: 'uppercase',
            letterSpacing: 1,
          }}
        >
          {label}
        </div>
      ))}
    </AbsoluteFill>
  );
};
