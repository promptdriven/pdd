import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
  staticFile,
  OffthreadVideo,
} from 'remotion';

// ── Inline constants (no external imports per project rules) ──

const BG_COLOR = '#0A1628';
const ACCENT_BLUE = '#3B82F6';
const ACCENT_GREEN = '#22C55E';
const ACCENT_RED = '#EF4444';
const TEXT_PRIMARY = '#FFFFFF';
const TEXT_SECONDARY = '#94A3B8';
const GLOW_BLUE = 'rgba(59, 130, 246, 0.35)';
const GLOW_GREEN = 'rgba(34, 197, 94, 0.35)';
const GLOW_RED = 'rgba(239, 68, 68, 0.35)';
const DIVIDER_COLOR = 'rgba(148, 163, 184, 0.75)';

const CYCLE_CENTER_X = 960;
const CYCLE_CENTER_Y = 500;
const CYCLE_RADIUS = 190;
const ICON_SIZE = 76;

// Phase timing
const PHASE_TEST_START = 25;
const PHASE_TEST_END = 100;
const PHASE_FIX_START = 100;
const PHASE_FIX_END = 180;
const PHASE_REGEN_START = 180;
const PHASE_REGEN_END = 250;
const PHASE_LOOP_START = 250;

interface PhaseConfig {
  label: string;
  color: string;
  glowColor: string;
  angleDeg: number;
  frameStart: number;
  frameEnd: number;
}

const PHASES: PhaseConfig[] = [
  {
    label: 'TEST',
    color: ACCENT_BLUE,
    glowColor: GLOW_BLUE,
    angleDeg: 210,
    frameStart: PHASE_TEST_START,
    frameEnd: PHASE_TEST_END,
  },
  {
    label: 'FIX',
    color: ACCENT_RED,
    glowColor: GLOW_RED,
    angleDeg: 330,
    frameStart: PHASE_FIX_START,
    frameEnd: PHASE_FIX_END,
  },
  {
    label: 'REGENERATE',
    color: ACCENT_GREEN,
    glowColor: GLOW_GREEN,
    angleDeg: 90,
    frameStart: PHASE_REGEN_START,
    frameEnd: PHASE_REGEN_END,
  },
];

// ── Sub-component: Phase icon node ──

const PhaseNode: React.FC<{
  phase: PhaseConfig;
  isActive: boolean;
  loopProgress: number;
}> = ({ phase, isActive, loopProgress }) => {
  const frame = useCurrentFrame();
  const { label, color, glowColor, angleDeg, frameStart } = phase;

  const angleRad = (angleDeg * Math.PI) / 180;
  const x = CYCLE_CENTER_X + CYCLE_RADIUS * Math.cos(angleRad) - ICON_SIZE / 2;
  const y = CYCLE_CENTER_Y + CYCLE_RADIUS * Math.sin(angleRad) - ICON_SIZE / 2;

  const entranceProgress = interpolate(frame, [frameStart, frameStart + 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(3)),
  });

  const scale = interpolate(entranceProgress, [0, 1], [0.3, 1]);
  const nodeOpacity = interpolate(entranceProgress, [0, 1], [0, 1]);

  const activeScale = isActive
    ? interpolate(
        frame,
        [phase.frameStart, phase.frameStart + 12, phase.frameEnd - 12, phase.frameEnd],
        [1, 1.18, 1.18, 1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
      )
    : 1;

  const glowOpacity = isActive ? 0.85 : 0.2 + loopProgress * 0.35;

  const labelY = y + ICON_SIZE + 16;
  const labelX = CYCLE_CENTER_X + CYCLE_RADIUS * Math.cos(angleRad);

  const renderIcon = () => {
    if (label === 'TEST') {
      return (
        <svg width={ICON_SIZE * 0.6} height={ICON_SIZE * 0.6} viewBox="0 0 80 80">
          <circle cx="35" cy="35" r="18" fill="none" stroke={color} strokeWidth="4.5" />
          <line x1="48" y1="48" x2="65" y2="65" stroke={color} strokeWidth="4.5" strokeLinecap="round" />
          <polyline points="25,36 33,44 47,28" fill="none" stroke={color} strokeWidth="3.5" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
      );
    }
    if (label === 'FIX') {
      return (
        <svg width={ICON_SIZE * 0.6} height={ICON_SIZE * 0.6} viewBox="0 0 80 80">
          <path
            d="M52 18 a16 16 0 0 0-24 24 l-13 13 a4.5 4.5 0 0 0 6.4 6.4 l13-13 a16 16 0 0 0 24-24 l-7 7-5.4-5.4z"
            fill="none"
            stroke={color}
            strokeWidth="4"
            strokeLinejoin="round"
          />
        </svg>
      );
    }
    return (
      <svg width={ICON_SIZE * 0.6} height={ICON_SIZE * 0.6} viewBox="0 0 80 80">
        <path d="M40 16 A24 24 0 0 1 62 44" fill="none" stroke={color} strokeWidth="4.5" strokeLinecap="round" />
        <polygon points="66,42 57,50 62,36" fill={color} />
        <path d="M40 64 A24 24 0 0 1 18 36" fill="none" stroke={color} strokeWidth="4.5" strokeLinecap="round" />
        <polygon points="14,38 23,30 18,44" fill={color} />
      </svg>
    );
  };

  return (
    <>
      {/* Glow */}
      <div
        style={{
          position: 'absolute',
          left: x - 24,
          top: y - 24,
          width: ICON_SIZE + 48,
          height: ICON_SIZE + 48,
          borderRadius: '50%',
          background: glowColor,
          filter: `blur(${isActive ? 28 : 16}px)`,
          opacity: glowOpacity * nodeOpacity,
          transform: `scale(${scale * activeScale})`,
        }}
      />
      {/* Circle node */}
      <div
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width: ICON_SIZE,
          height: ICON_SIZE,
          borderRadius: '50%',
          border: `3px solid ${color}`,
          background: isActive ? `${color}20` : 'rgba(10, 22, 40, 0.92)',
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          opacity: nodeOpacity,
          transform: `scale(${scale * activeScale})`,
          boxShadow: isActive ? `0 0 24px ${glowColor}` : 'none',
        }}
      >
        {renderIcon()}
      </div>
      {/* Label */}
      <div
        style={{
          position: 'absolute',
          left: labelX - 90,
          top: labelY,
          width: 180,
          textAlign: 'center',
          fontFamily: 'Inter, system-ui, sans-serif',
          fontWeight: 700,
          fontSize: 20,
          letterSpacing: '0.14em',
          color: isActive ? color : 'rgba(255,255,255,0.82)',
          opacity: nodeOpacity * 0.92,
          transform: `scale(${scale})`,
          textShadow: isActive ? `0 0 14px ${glowColor}` : 'none',
        }}
      >
        {label}
      </div>
    </>
  );
};

// ── Sub-component: Arc between phases ──

const PhaseArc: React.FC<{
  fromAngleDeg: number;
  toAngleDeg: number;
  color: string;
  appearFrame: number;
  travelFrame: number;
  travelDuration: number;
}> = ({ fromAngleDeg, toAngleDeg, color, appearFrame, travelFrame, travelDuration }) => {
  const frame = useCurrentFrame();

  const arcOpacity = interpolate(frame, [appearFrame, appearFrame + 12], [0, 0.78], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const dotProgress = interpolate(
    frame,
    [travelFrame, travelFrame + travelDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.poly(3)) },
  );

  const arcR = CYCLE_RADIUS + 44;
  const fromRad = (fromAngleDeg * Math.PI) / 180;
  const toRad = (toAngleDeg * Math.PI) / 180;

  const startX = CYCLE_CENTER_X + arcR * Math.cos(fromRad);
  const startY = CYCLE_CENTER_Y + arcR * Math.sin(fromRad);
  const endX = CYCLE_CENTER_X + arcR * Math.cos(toRad);
  const endY = CYCLE_CENTER_Y + arcR * Math.sin(toRad);

  let angleDiff = toAngleDeg - fromAngleDeg;
  if (angleDiff < 0) angleDiff += 360;
  const largeArc = angleDiff > 180 ? 1 : 0;

  // Dot position
  const normalizedFrom = ((fromAngleDeg % 360) + 360) % 360;
  const normalizedTo = ((toAngleDeg % 360) + 360) % 360;
  let sweep = normalizedTo - normalizedFrom;
  if (sweep < 0) sweep += 360;
  const currentAngleDeg = normalizedFrom + sweep * dotProgress;
  const dotRad = (currentAngleDeg * Math.PI) / 180;
  const dotX = CYCLE_CENTER_X + arcR * Math.cos(dotRad);
  const dotY = CYCLE_CENTER_Y + arcR * Math.sin(dotRad);

  const pathD = `M ${startX} ${startY} A ${arcR} ${arcR} 0 ${largeArc} 1 ${endX} ${endY}`;

  // Arrow head at end
  const arrowAngle = toRad + Math.PI / 2;
  const arrowS = 10;

  return (
    <svg
      style={{ position: 'absolute', left: 0, top: 0, width: 1920, height: 1080, pointerEvents: 'none' }}
    >
      <path d={pathD} fill="none" stroke={color} strokeWidth="2.5" strokeDasharray="8 5" opacity={arcOpacity} />
      <polygon
        points={`
          ${endX},${endY}
          ${endX - arrowS * Math.cos(arrowAngle - 0.45)},${endY - arrowS * Math.sin(arrowAngle - 0.45)}
          ${endX - arrowS * Math.cos(arrowAngle + 0.45)},${endY - arrowS * Math.sin(arrowAngle + 0.45)}
        `}
        fill={color}
        opacity={arcOpacity}
      />
      {dotProgress > 0.01 && dotProgress < 0.99 && (
        <circle cx={dotX} cy={dotY} r={5} fill={color} opacity={0.95} />
      )}
    </svg>
  );
};

// ── Sub-component: Subtitle bar ──

const SubtitleBar: React.FC<{
  text: string;
  startFrame: number;
  endFrame: number;
  color: string;
}> = ({ text, startFrame, endFrame, color }) => {
  const frame = useCurrentFrame();

  const visible = frame >= startFrame && frame <= endFrame;
  if (!visible) return null;

  const fadeIn = interpolate(frame, [startFrame, startFrame + 8], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const fadeOut = interpolate(frame, [endFrame - 8, endFrame], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const opacity = Math.min(fadeIn, fadeOut);

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 80,
        left: 0,
        width: 1920,
        display: 'flex',
        justifyContent: 'center',
        opacity,
      }}
    >
      <div
        style={{
          background: 'rgba(10, 22, 40, 0.88)',
          borderLeft: `4px solid ${color}`,
          borderRadius: 8,
          padding: '14px 32px',
          fontFamily: 'Inter, system-ui, sans-serif',
          fontSize: 26,
          fontWeight: 600,
          color: TEXT_PRIMARY,
          letterSpacing: '0.02em',
          maxWidth: 900,
          textAlign: 'center',
        }}
      >
        {text}
      </div>
    </div>
  );
};

// ── Main Component ──

export const defaultColdOpen09TestFixRegenerateProps = {};

export const ColdOpen09TestFixRegenerate: React.FC = () => {
  const frame = useCurrentFrame();
  const { durationInFrames } = useVideoConfig();

  // Determine active phase
  const activePhaseIdx =
    frame >= PHASE_REGEN_START
      ? 2
      : frame >= PHASE_FIX_START
        ? 1
        : frame >= PHASE_TEST_START
          ? 0
          : -1;

  // Loop convergence (all three glow together at end)
  const loopProgress = interpolate(frame, [PHASE_LOOP_START, durationInFrames], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Title animation
  const titleOpacity = interpolate(frame, [0, 18], [0.85, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const titleY = interpolate(frame, [0, 18], [4, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(3)),
  });

  // Center cycle label
  const cycleLabelOpacity = interpolate(frame, [PHASE_LOOP_START, PHASE_LOOP_START + 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const cycleLabelScale = interpolate(frame, [PHASE_LOOP_START, PHASE_LOOP_START + 20], [0.7, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(3)),
  });

  // Background video opacity
  const bgVideoOpacity = interpolate(frame, [0, 15], [0.12, 0.18], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Rotating ring animation during loop phase
  const ringRotation = interpolate(frame, [PHASE_LOOP_START, durationInFrames], [0, 360], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const ringOpacity = interpolate(frame, [PHASE_LOOP_START, PHASE_LOOP_START + 20], [0, 0.4], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR, overflow: 'hidden' }}>
      {/* Background video */}
      <div style={{ position: 'absolute', top: 0, left: 0, width: 1920, height: 1080, opacity: bgVideoOpacity }}>
        <OffthreadVideo
          src={staticFile('veo/code_glowing_output.mp4')}
          style={{ width: '100%', height: '100%', objectFit: 'cover' }}
          muted
        />
      </div>

      {/* Gradient overlay */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: 1920,
          height: 1080,
          background: `radial-gradient(ellipse 70% 60% at 50% 50%, transparent 30%, ${BG_COLOR} 100%)`,
        }}
      />

      {/* Title */}
      <div
        style={{
          position: 'absolute',
          top: 52,
          left: 0,
          width: 1920,
          textAlign: 'center',
          opacity: titleOpacity,
          transform: `translateY(${titleY}px)`,
        }}
      >
        <div
          style={{
            fontFamily: 'Inter, system-ui, sans-serif',
            fontSize: 48,
            fontWeight: 800,
            color: TEXT_PRIMARY,
            letterSpacing: '0.04em',
            textShadow: '0 2px 20px rgba(0,0,0,0.5)',
          }}
        >
          The Cycle
        </div>
        {/* Divider */}
        <div
          style={{
            width: 120,
            height: 3,
            background: DIVIDER_COLOR,
            margin: '12px auto 0',
            borderRadius: 2,
            opacity: 0.8,
          }}
        />
      </div>

      {/* Subtitle text */}
      <div
        style={{
          position: 'absolute',
          top: 130,
          left: 0,
          width: 1920,
          textAlign: 'center',
          opacity: titleOpacity * 0.78,
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, system-ui, sans-serif',
            fontSize: 22,
            fontWeight: 500,
            color: TEXT_SECONDARY,
            letterSpacing: '0.06em',
          }}
        >
          TEST &nbsp;&bull;&nbsp; FIX &nbsp;&bull;&nbsp; REGENERATE
        </span>
      </div>

      {/* Rotating outer ring during loop phase */}
      <svg
        style={{
          position: 'absolute',
          left: CYCLE_CENTER_X - CYCLE_RADIUS - 70,
          top: CYCLE_CENTER_Y - CYCLE_RADIUS - 70,
          width: (CYCLE_RADIUS + 70) * 2,
          height: (CYCLE_RADIUS + 70) * 2,
          pointerEvents: 'none',
          opacity: ringOpacity,
          transform: `rotate(${ringRotation}deg)`,
        }}
      >
        <circle
          cx={CYCLE_RADIUS + 70}
          cy={CYCLE_RADIUS + 70}
          r={CYCLE_RADIUS + 56}
          fill="none"
          stroke="rgba(148, 163, 184, 0.3)"
          strokeWidth="1.5"
          strokeDasharray="12 8 4 8"
        />
      </svg>

      {/* Arcs connecting phases */}
      <PhaseArc
        fromAngleDeg={210}
        toAngleDeg={330}
        color={ACCENT_BLUE}
        appearFrame={PHASE_TEST_END - 20}
        travelFrame={PHASE_TEST_END - 15}
        travelDuration={25}
      />
      <PhaseArc
        fromAngleDeg={330}
        toAngleDeg={90}
        color={ACCENT_RED}
        appearFrame={PHASE_FIX_END - 20}
        travelFrame={PHASE_FIX_END - 15}
        travelDuration={25}
      />
      <PhaseArc
        fromAngleDeg={90}
        toAngleDeg={210}
        color={ACCENT_GREEN}
        appearFrame={PHASE_REGEN_END - 20}
        travelFrame={PHASE_REGEN_END - 15}
        travelDuration={25}
      />

      {/* Phase nodes */}
      {PHASES.map((phase, idx) => (
        <PhaseNode
          key={phase.label}
          phase={phase}
          isActive={activePhaseIdx === idx}
          loopProgress={loopProgress}
        />
      ))}

      {/* Center cycle label (appears at loop phase) */}
      <div
        style={{
          position: 'absolute',
          left: CYCLE_CENTER_X - 80,
          top: CYCLE_CENTER_Y - 28,
          width: 160,
          height: 56,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          opacity: cycleLabelOpacity,
          transform: `scale(${cycleLabelScale})`,
        }}
      >
        <div
          style={{
            fontFamily: 'Inter, system-ui, sans-serif',
            fontSize: 28,
            fontWeight: 800,
            color: TEXT_PRIMARY,
            letterSpacing: '0.08em',
            textShadow: '0 0 20px rgba(59, 130, 246, 0.5), 0 0 40px rgba(34, 197, 94, 0.3)',
          }}
        >
          CYCLE
        </div>
      </div>

      {/* Phase description subtitles */}
      <SubtitleBar
        text="Run your tests — discover what's broken"
        startFrame={PHASE_TEST_START + 5}
        endFrame={PHASE_TEST_END - 5}
        color={ACCENT_BLUE}
      />
      <SubtitleBar
        text="Fix the issue — patch, refactor, or rethink"
        startFrame={PHASE_FIX_START + 5}
        endFrame={PHASE_FIX_END - 5}
        color={ACCENT_RED}
      />
      <SubtitleBar
        text="Regenerate — let AI rebuild with full context"
        startFrame={PHASE_REGEN_START + 5}
        endFrame={PHASE_REGEN_END - 5}
        color={ACCENT_GREEN}
      />
      <SubtitleBar
        text="The loop continues — each pass makes the output stronger"
        startFrame={PHASE_LOOP_START + 10}
        endFrame={295}
        color={TEXT_PRIMARY}
      />

      {/* Bottom progress bar */}
      <div
        style={{
          position: 'absolute',
          bottom: 30,
          left: 160,
          width: 1600,
          height: 4,
          background: 'rgba(148, 163, 184, 0.15)',
          borderRadius: 2,
        }}
      >
        <div
          style={{
            width: `${(frame / durationInFrames) * 100}%`,
            height: '100%',
            borderRadius: 2,
            background: `linear-gradient(90deg, ${ACCENT_BLUE}, ${ACCENT_RED}, ${ACCENT_GREEN})`,
            opacity: 0.8,
          }}
        />
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen09TestFixRegenerate;
