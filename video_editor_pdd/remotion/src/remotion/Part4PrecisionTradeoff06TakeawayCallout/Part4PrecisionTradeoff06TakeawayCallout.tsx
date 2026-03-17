import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  spring,
  useVideoConfig,
} from 'remotion';
import {
  BG_COLOR,
  TEXT_COLOR,
  TEXT_OPACITY,
  AMBER,
  FONT_FAMILY,
  BASE_FONT_SIZE,
  LESS_FONT_SIZE,
  LINE1_Y,
  LINE2_Y,
  LINE3_Y,
  MINI_ANIM_Y,
  LINE1_START,
  LINE2_START,
  LINE3_START,
  MINI_ANIM_START,
  PULSE_START,
  PULSE_DURATION,
  WORD_STAGGER_FRAMES,
} from './constants';
import { WallIcon } from './WallIcon';
import { InverseAnimation } from './InverseAnimation';

export const defaultPart4PrecisionTradeoff06TakeawayCalloutProps = {};

// ─── Helper: per-word opacity ────────────────────────────────────────────────

function wordOpacity(localFrame: number, wordIndex: number): number {
  const start = wordIndex * WORD_STAGGER_FRAMES;
  return interpolate(localFrame, [start, start + 10], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });
}

function wordTranslateY(localFrame: number, wordIndex: number): number {
  const start = wordIndex * WORD_STAGGER_FRAMES;
  return interpolate(localFrame, [start, start + 10], [6, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });
}

// ─── Shared text styles ──────────────────────────────────────────────────────

const baseStyle: React.CSSProperties = {
  fontFamily: FONT_FAMILY,
  fontSize: BASE_FONT_SIZE,
  fontWeight: 400,
  color: TEXT_COLOR,
  opacity: TEXT_OPACITY,
  lineHeight: 1,
  whiteSpace: 'pre',
};

// ─── Main Component ──────────────────────────────────────────────────────────

export const Part4PrecisionTradeoff06TakeawayCallout: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // ── Subtle vignette overlay fades in over first 15 frames ──────────────
  // Background is always fully visible from frame 0 per requirements.
  const vignetteOpacity = interpolate(frame, [0, 15], [0.3, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // ── LINE 1: "The more **walls** you have," ─────────────────────────────
  const l1Frame = Math.max(0, frame - LINE1_START);

  // ── LINE 2: "the **less** you need to specify." ────────────────────────
  const l2Frame = Math.max(0, frame - LINE2_START);

  // "less" spring scale
  const lessScale =
    frame >= LINE2_START
      ? spring({
          frame: frame - LINE2_START - 1 * WORD_STAGGER_FRAMES, // "less" is word index 1
          fps,
          config: { stiffness: 200, damping: 15 },
        }) *
          0.1 +
        1
      : 1;

  // ── LINE 3: "The **mold** does the precision work." ────────────────────
  const l3Frame = Math.max(0, frame - LINE3_START);

  // "mold" glow ramp
  const moldGlow =
    frame >= LINE3_START
      ? interpolate(
          frame - LINE3_START,
          [WORD_STAGGER_FRAMES * 1, WORD_STAGGER_FRAMES * 1 + 15],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.inOut(Easing.sin),
          },
        )
      : 0;

  // "precision work" pulse at end
  const pulseRaw =
    frame >= PULSE_START
      ? interpolate(
          frame - PULSE_START,
          [0, PULSE_DURATION / 2, PULSE_DURATION],
          [1, 1.06, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.inOut(Easing.sin),
          },
        )
      : 1;

  // Mini animation local frame
  const miniFrame = Math.max(0, frame - MINI_ANIM_START);

  // ── Shared line container style ────────────────────────────────────────
  const lineContainer = (y: number): React.CSSProperties => ({
    position: 'absolute',
    top: y,
    left: 0,
    right: 0,
    display: 'flex',
    justifyContent: 'center',
    alignItems: 'baseline',
  });

  // Word wrapper
  const w = (
    localFrame: number,
    idx: number,
    children: React.ReactNode,
    extraStyle?: React.CSSProperties,
  ): React.ReactNode => (
    <span
      key={idx}
      style={{
        display: 'inline-block',
        opacity: wordOpacity(localFrame, idx),
        transform: `translateY(${wordTranslateY(localFrame, idx)}px)`,
        ...extraStyle,
      }}
    >
      {children}
    </span>
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
      }}
    >
      {/* Subtle vignette overlay that fades out — gives "clean slate" feel */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          background: `radial-gradient(ellipse at center, transparent 40%, rgba(0,0,0,${vignetteOpacity}) 100%)`,
          pointerEvents: 'none',
          zIndex: 10,
        }}
      />
      {/* ── LINE 1 ────────────────────────────────────────────────── */}
      {frame >= LINE1_START && (
        <div style={lineContainer(LINE1_Y)}>
          <span style={baseStyle}>
            {w(l1Frame, 0, 'The ')}
            {w(l1Frame, 1, 'more ')}
            {w(
              l1Frame,
              2,
              <span
                style={{
                  display: 'inline-flex',
                  alignItems: 'center',
                  gap: 4,
                }}
              >
                <WallIcon size={8} color={AMBER} />
                <span style={{ fontWeight: 700, color: AMBER, opacity: 1 }}>
                  walls
                </span>
              </span>,
            )}
            {w(l1Frame, 3, ' you ')}
            {w(l1Frame, 4, 'have,')}
          </span>
        </div>
      )}

      {/* ── LINE 2 ────────────────────────────────────────────────── */}
      {frame >= LINE2_START && (
        <div style={lineContainer(LINE2_Y)}>
          <span style={baseStyle}>
            {w(l2Frame, 0, 'the ')}
            {w(
              l2Frame,
              1,
              <span
                style={{
                  fontWeight: 700,
                  fontSize: LESS_FONT_SIZE,
                  color: TEXT_COLOR,
                  opacity: 1,
                  display: 'inline-block',
                  transform: `scale(${lessScale})`,
                  transformOrigin: 'center baseline',
                }}
              >
                less
              </span>,
            )}
            {w(l2Frame, 2, ' you ')}
            {w(l2Frame, 3, 'need ')}
            {w(l2Frame, 4, 'to ')}
            {w(l2Frame, 5, 'specify.')}
          </span>
        </div>
      )}

      {/* ── LINE 3 ────────────────────────────────────────────────── */}
      {frame >= LINE3_START && (
        <div style={lineContainer(LINE3_Y)}>
          <span style={baseStyle}>
            {w(l3Frame, 0, 'The ')}
            {w(
              l3Frame,
              1,
              <span
                style={{
                  fontWeight: 700,
                  color: AMBER,
                  opacity: 1,
                  textShadow: `0 0 ${12 * moldGlow}px rgba(217, 148, 74, ${0.15 * moldGlow})`,
                }}
              >
                mold
              </span>,
            )}
            {w(l3Frame, 2, ' does ')}
            {w(l3Frame, 3, 'the ')}
            {w(
              l3Frame,
              4,
              <span
                style={{
                  fontWeight: 600,
                  color: TEXT_COLOR,
                  opacity: 1,
                  display: 'inline-block',
                  transform: `scale(${pulseRaw})`,
                  transformOrigin: 'center baseline',
                }}
              >
                precision work
              </span>,
            )}
            {w(l3Frame, 5, '.')}
          </span>
        </div>
      )}

      {/* ── MINI INVERSE ANIMATION ────────────────────────────────── */}
      {frame >= MINI_ANIM_START && (
        <div
          style={{
            position: 'absolute',
            top: MINI_ANIM_Y,
            left: 0,
            right: 0,
            display: 'flex',
            justifyContent: 'center',
          }}
        >
          <InverseAnimation localFrame={miniFrame} />
        </div>
      )}
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff06TakeawayCallout;
