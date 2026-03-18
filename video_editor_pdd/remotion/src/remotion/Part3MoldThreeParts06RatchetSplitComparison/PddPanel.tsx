import React from 'react';
import { useCurrentFrame, interpolate, spring, useVideoConfig, Easing } from 'remotion';
import {
  BG_RIGHT_PANEL,
  GREEN,
  RED,
  AMBER,
  TEXT_SECONDARY,
  PANEL_WIDTH,
  ROW_HEIGHT,
  HEADER_Y,
  PDD_ROWS,
  FRAME,
} from './constants';

// ── Icon components ──
const AlertIcon: React.FC = () => (
  <svg width="16" height="16" viewBox="0 0 16 16">
    <circle cx="8" cy="8" r="7" fill="none" stroke={RED} strokeWidth="1.5" />
    <line x1="8" y1="4" x2="8" y2="9" stroke={RED} strokeWidth="2" strokeLinecap="round" />
    <circle cx="8" cy="12" r="1.2" fill={RED} />
  </svg>
);

const WallIcon: React.FC = () => (
  <svg width="16" height="16" viewBox="0 0 16 16">
    <rect x="2" y="3" width="12" height="10" fill="none" stroke={AMBER} strokeWidth="1.5" rx="1" />
    <line x1="2" y1="8" x2="14" y2="8" stroke={AMBER} strokeWidth="1" />
    <line x1="8" y1="3" x2="8" y2="8" stroke={AMBER} strokeWidth="1" />
    <line x1="5" y1="8" x2="5" y2="13" stroke={AMBER} strokeWidth="1" />
    <line x1="11" y1="8" x2="11" y2="13" stroke={AMBER} strokeWidth="1" />
  </svg>
);

const CheckIcon: React.FC<{ scale: number }> = ({ scale }) => (
  <svg
    width="16"
    height="16"
    viewBox="0 0 16 16"
    style={{ transform: `scale(${scale})` }}
  >
    <circle cx="8" cy="8" r="7" fill={GREEN} opacity={0.2} />
    <path
      d="M4.5 8.5 L7 11 L11.5 5.5"
      fill="none"
      stroke={GREEN}
      strokeWidth="2"
      strokeLinecap="round"
      strokeLinejoin="round"
    />
  </svg>
);

// ── Mini Mold cross-section ──
const MiniMold: React.FC<{ opacity: number }> = ({ opacity }) => (
  <div
    style={{
      position: 'absolute',
      left: PANEL_WIDTH / 2 - 40,
      top: 380,
      width: 80,
      height: 100,
      opacity,
    }}
  >
    <svg width="80" height="100" viewBox="0 0 80 100">
      {/* Outer mold shape */}
      <rect x="5" y="5" width="70" height="90" rx="4" fill="none" stroke={AMBER} strokeWidth="1.5" opacity={0.4} />
      {/* Inner cavity */}
      <rect x="20" y="20" width="40" height="60" rx="2" fill={BG_RIGHT_PANEL} stroke={GREEN} strokeWidth="1" opacity={0.5} />
      {/* Existing walls */}
      <line x1="30" y1="20" x2="30" y2="80" stroke={GREEN} strokeWidth="1" opacity={0.4} />
      <line x1="50" y1="20" x2="50" y2="80" stroke={GREEN} strokeWidth="1" opacity={0.4} />
      {/* New wall being added — amber, brighter */}
      <line x1="40" y1="20" x2="40" y2="80" stroke={AMBER} strokeWidth="2" opacity={0.8} />
      {/* Label */}
      <text x="40" y="96" textAnchor="middle" fill={AMBER} fontSize="7" fontFamily="Inter, sans-serif" opacity={0.6}>
        null check
      </text>
    </svg>
  </div>
);

// ── Single PDD Row ──
const PddRow: React.FC<{
  text: string;
  icon: 'alert' | 'wall' | 'check';
  index: number;
  checkScale: number;
}> = ({ text, icon, index, checkScale }) => {
  const frame = useCurrentFrame();
  const startFrames = [FRAME.RIGHT_ROW_1_START, FRAME.RIGHT_ROW_2_START, FRAME.RIGHT_ROW_3_START];
  const appearFrame = startFrames[index] ?? 0;

  const opacity = interpolate(frame, [appearFrame, appearFrame + 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const slideX = interpolate(frame, [appearFrame, appearFrame + 15], [-20, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const isTerminal = icon === 'wall' || icon === 'check';
  const y = 80 + index * ROW_HEIGHT;

  // Glow for the check row
  const glowOpacity = icon === 'check'
    ? interpolate(frame, [appearFrame + 15, appearFrame + 30], [0, 0.15], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      })
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: 30,
        top: y,
        width: PANEL_WIDTH - 60,
        height: ROW_HEIGHT,
        opacity,
        transform: `translateX(${slideX}px)`,
        display: 'flex',
        alignItems: 'center',
        gap: 12,
        backgroundColor: glowOpacity > 0 ? `rgba(90, 170, 110, ${glowOpacity})` : 'transparent',
        borderRadius: 6,
        padding: '0 8px',
      }}
    >
      {/* Icon */}
      <div
        style={{
          width: 20,
          height: 20,
          flexShrink: 0,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
        }}
      >
        {icon === 'alert' && <AlertIcon />}
        {icon === 'wall' && <WallIcon />}
        {icon === 'check' && <CheckIcon scale={checkScale} />}
      </div>

      {/* Text */}
      <div
        style={{
          fontFamily: isTerminal ? 'JetBrains Mono, monospace' : 'JetBrains Mono, monospace',
          fontSize: 12,
          color: icon === 'check' ? GREEN : TEXT_SECONDARY,
          whiteSpace: 'nowrap',
          overflow: 'hidden',
          textOverflow: 'ellipsis',
        }}
      >
        {text}
      </div>
    </div>
  );
};

// ── Full PDD Panel ──
export const PddPanel: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Header fade
  const headerOpacity = interpolate(frame, [0, FRAME.HEADERS_DUR], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Spring scale for the checkmark
  const checkScale = spring({
    frame: Math.max(0, frame - FRAME.RIGHT_ROW_3_START - 10),
    fps,
    config: { stiffness: 180, damping: 10 },
  });

  // Subtitle "Bug impossible forever ∞"
  const subtitleOpacity = interpolate(
    frame,
    [FRAME.PDD_SUBTITLE_START, FRAME.PDD_SUBTITLE_START + 20],
    [0, 0.8],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const subtitleScale = spring({
    frame: Math.max(0, frame - FRAME.PDD_SUBTITLE_START),
    fps,
    config: { stiffness: 180, damping: 10 },
  });

  // Mini mold icon
  const moldOpacity = interpolate(
    frame,
    [FRAME.PDD_MOLD_START, FRAME.PDD_MOLD_START + 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 962,
        top: 0,
        width: PANEL_WIDTH,
        height: '100%',
        backgroundColor: BG_RIGHT_PANEL,
        overflow: 'hidden',
      }}
    >
      {/* Header */}
      <div
        style={{
          position: 'absolute',
          top: HEADER_Y,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: GREEN,
          opacity: headerOpacity,
          letterSpacing: 2,
        }}
      >
        PDD
      </div>

      {/* Rows */}
      {PDD_ROWS.map((row, i) => (
        <PddRow
          key={i}
          text={row.text}
          icon={row.icon}
          index={i}
          checkScale={checkScale}
        />
      ))}

      {/* Subtitle: "Bug impossible forever ∞" */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 280,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 700,
          color: GREEN,
          opacity: subtitleOpacity,
          transform: `scale(${subtitleScale})`,
        }}
      >
        Bug impossible forever ∞
      </div>

      {/* Mini mold */}
      <MiniMold opacity={moldOpacity} />
    </div>
  );
};

export default PddPanel;
